-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch189_Segment000
-- name    : Polychromatic418967fa_Branch189_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:29:20.718628+00:00
-- url     : https://prove2.me/theorems/d7d61f06-72f8-40e1-8dfe-c0c9984e00ab
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_189_segment_000 : allB 100 189 :=
  allB_succ' 91 99 189 (Eq.refl Bool.true) (allA_succ_of_gcd 90 99 189 9 10 11 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 89 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 99 189 (Polychromatic418967fa.accept_13_10_8_7_1_1074 88 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 99 189 3 29 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 85 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 99 189 3 28 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 99 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 83 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 189 9 9 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 189
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 80 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 79 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 99 189 3 26 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 99 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 77
  99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 189
  (Polychromatic418967fa.accept_14_6_1_7_1_2775 76 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 99 189 3 25 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 73 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 189 9 8 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 71 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 99 189 3 23 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 99 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135
  68 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 67 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 99 189 3 22 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 99 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 65 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 189 (Polychromatic418967fa.accept_13_12_8_7_1_2526 64 99
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 189 9 7 11 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 99 189 3 20 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 99 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  59 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 99 189 3 19 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 99 189 (Polychromatic418967fa.accept_16_8_3_13_1_7295 56 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 189 9 6 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 53 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 189 (Polychromatic418967fa.accept_19_14_4_18_1_6665 52 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 99 189 3 17 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 99 189 3 16 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 99 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 189 9 5 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 189
  (Polychromatic418967fa.accept_20_4_19_9_1_7961 44 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 99 189 3 14 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 99 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 41
  99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 189
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 40 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 99 189 3 13 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 189 9 4 11 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 189 3 11 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 189
  (Polychromatic418967fa.accept_20_12_19_9_1_10936 32 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 99 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 99 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 189 3 10 33 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 189 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 189 9 3 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 189 3 8 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 189 3 7 33 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 189
  (Polychromatic418967fa.accept_14_6_1_7_1_2775 20 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 189 9 2 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 189
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 189 3 5 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 189 3 4 33 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 189 9 1 11 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 189 (Polychromatic418967fa.accept_14_8_1_7_1_3725 8 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 189 3 2 33 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 189 (Polychromatic418967fa.accept_20_4_19_9_1_7961 4 99 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 189 3 1 33 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 99 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 98 189
  (Eq.refl Bool.true) (allA_succ_of_gcd 91 98 189 7 13 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 90 98 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 90 98 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 98 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 98 189 (accept_3_4 88 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 98 189 (Polychromatic418967fa.accept_17_1_13_2_1_7086 86 98 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 98 189 (accept_3_4 85 98 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98 189 7 12 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 83
  98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 189 (accept_3_4 82 98
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 189
  (Polychromatic418967fa.accept_10_1_8_9_1_787 81 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 98 189 (Polychromatic418967fa.accept_19_4_3_18_1_2699 80 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 98 189 (accept_3_4 79 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 98 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 78 98 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 98 189 7 11 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 98 189 (accept_3_4 76 98 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 74 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 189 (accept_3_4 73 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 189 (Polychromatic418967fa.accept_19_15_3_18_1_5241 72 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 189 7 10 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 189
  (Polychromatic418967fa.accept_16_5_2_13_1_1007 69 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 98 189 (Polychromatic418967fa.accept_19_11_3_18_1_10828 68 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 98 189 (accept_3_4 67 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 98 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 98 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 98 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 65
  98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 189 (accept_3_4 64 98
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 98 189 7 9 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 98 189
  (Polychromatic418967fa.accept_15_2_8_9_1_4294 62 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 189 (accept_3_4 61 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 189 (Polychromatic418967fa.accept_18_6_8_9_1_1960 60 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 189 (accept_3_4 58 98 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 57 98 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 189 7 8 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 189 (accept_3_4 55 98 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 98 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 98 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 98 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 98 189 (accept_3_4 52 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 98 189 (Polychromatic418967fa.accept_23_4_6_5_1_10935 50 98 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 98 189 7 7 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 98 189
  (Polychromatic418967fa.accept_15_3_8_9_1_795 48 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 189 (accept_3_4 46 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 98 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 98 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 189 (Polychromatic418967fa.accept_10_4_8_9_1_784
  44 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 98 189 (accept_3_4 43
  98 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 189 7 6 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 98 189 (accept_3_4 40 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 98 189 (Polychromatic418967fa.accept_26_12_20_7_1_10934 38 98 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 98 189 (accept_3_4 37 98 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 98 189 (Polychromatic418967fa.accept_28_8_14_21_1_10933 36 98
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 98 189 7 5 14 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 98 189 (accept_3_4 34
  98 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 189
  (Polychromatic418967fa.accept_15_3_8_9_1_795 33 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 98 189 (Polychromatic418967fa.accept_15_2_8_9_1_4294 32 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 98 189 (accept_3_4 31 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 98 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 98 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 98 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29
  98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 189 7 4 14 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 98 189 (Polychromatic418967fa.accept_23_3_6_5_1_10932 26 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 98 189 (accept_3_4 25 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 98 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 98 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 189 (accept_3_4 22 98
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 98 189 7 3 14 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 98 189
  (Polychromatic418967fa.accept_28_20_14_21_1_10931 20 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 98 189 (accept_3_4 19 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 98 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 98 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 98 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 189 (accept_3_4 16 98 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 189 7 2 14 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 189 (accept_3_4 13
  98 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 98 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 189 (accept_3_4 10 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 98 189 (Polychromatic418967fa.accept_19_9_3_18_1_5263 9 98 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 189
  (Polychromatic418967fa.accept_25_8_23_14_1_10930 8 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 98 189 7 1 14 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 98 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 98 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 98 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 189 (accept_3_4 4 98 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 189
  (Polychromatic418967fa.accept_15_2_8_9_1_4294 2 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 189 (accept_3_4 1 98 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 97 189
  (Eq.refl Bool.true) (allA_succ_of_accept 92 97 189 (accept_3_5 92 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 97 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 91 97 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 189 (Polychromatic418967fa.accept_13_12_6_7_1_1071 90 97
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 189 (accept_3_5 89 97 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 88
  97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 87 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 97 189 (accept_3_5 86 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  97 189 (Polychromatic418967fa.accept_14_1_13_7_1_1205 85 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 97 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 189 (accept_3_5 83 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 189
  (Polychromatic418967fa.accept_11_4_9_2_1_259 81 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 97 189 (accept_3_5 80 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  97 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 79 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 97 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 78 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 189 (accept_3_5 77 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 75 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 97 189 (accept_3_5 74 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  97 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 73 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 189 (accept_3_5 71 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 189
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 69 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 189 (accept_3_5 68 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 189 (Polychromatic418967fa.accept_16_3_1_13_1_4968 67 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 66 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 189 (accept_3_5 65 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 63 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 189 (accept_3_5 62 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 61 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 189 (accept_3_5 59 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 189
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 57 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 189 (accept_3_5 56 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 189 (Polychromatic418967fa.accept_17_4_12_2_1_2349 55 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 189 (Polychromatic418967fa.accept_19_16_2_18_1_8136 54 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 189 (accept_3_5 53 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 189
  (Polychromatic418967fa.accept_11_7_9_2_1_260 51 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 189 (accept_3_5 50 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 189 (Polychromatic418967fa.accept_25_24_22_14_1_10929 49 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 189 (accept_3_5 47 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 189
  (Polychromatic418967fa.accept_22_1_9_13_1_2894 45 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 189 (accept_3_5 44 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 43 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 189 (accept_3_5 41 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 189 (accept_3_5 38 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 189 (accept_3_5 35 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 189
  (Polychromatic418967fa.accept_22_11_9_13_1_10928 33 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 97 189 (accept_3_5 32 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 97 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 31 97 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 30 97 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 189 (accept_3_5 29 97 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 189 (accept_3_5 26 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 189 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 189 (Polychromatic418967fa.accept_17_7_12_2_1_7105 24 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 189 (accept_3_5 23 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 97 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 189
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 21 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 189 (accept_3_5 20 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 189 (Polychromatic418967fa.accept_16_3_1_13_1_4968 19 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 189 (accept_3_5 17 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 189
  (Polychromatic418967fa.accept_11_4_9_2_1_259 15 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 189 (accept_3_5 14 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 189 (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 189 (accept_3_5 11 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 97 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 189
  (Polychromatic418967fa.accept_13_9_6_7_1_551 9 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 189 (accept_3_5 8 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  189 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 189 (Polychromatic418967fa.accept_14_6_13_7_1_2015 6 97 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 189 (accept_3_5 5 97 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 3
  97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 189 (accept_3_5 2 97 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 1
  97 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 96 189
  (Eq.refl Bool.true) (allA_succ_of_gcd 93 96 189 3 31 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 92 96 189 (Polychromatic418967fa.accept_18_2_6_9_1_1032 92 96 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 189
  (Polychromatic418967fa.accept_15_1_6_9_1_254 91 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 96 189 3 30 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 96 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 89 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 96 189 (Polychromatic418967fa.accept_17_3_11_2_1_8435 88 96
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 96 189 3 29 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 96 189
  (Polychromatic418967fa.accept_14_2_12_7_1_617 86 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 96 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 85 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 189 3 28 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 83
  96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 96 189
  (Polychromatic418967fa.accept_11_5_8_2_1_588 82 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 96 189 3 27 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 96 189 (Polychromatic418967fa.accept_13_2_5_7_1_1695 80 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 189 (Polychromatic418967fa.accept_14_9_12_7_1_597 79 96 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 189 3 26 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 189
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 77 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 96 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 76 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 96 189 3 25 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 96 189 (Polychromatic418967fa.accept_15_14_6_9_1_2274
  74 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 189
  (Polychromatic418967fa.accept_10_3_6_9_1_779 73 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 96 189 3 24 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 96 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 71 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 189 (Polychromatic418967fa.accept_19_13_1_18_1_5279 70 96
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 96 189 3 23 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 96 189
  (Polychromatic418967fa.accept_18_14_6_9_1_1950 68 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 96 189 (Polychromatic418967fa.accept_13_2_5_7_1_1695 67 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 189 3 22 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235
  65 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 189
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 64 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 96 189 3 21 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 96 189 (Polychromatic418967fa.accept_18_8_6_9_1_5576 62 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 189 (Polychromatic418967fa.accept_14_5_12_7_1_2767 61 96
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 189 3 20 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 189
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 59 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 96 189 (Polychromatic418967fa.accept_14_2_12_7_1_617 58 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 96 189 3 19 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 96 189 (Polychromatic418967fa.accept_15_11_6_9_1_3236
  56 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 189
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 55 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 96 189 3 18 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 96 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 189 (Polychromatic418967fa.accept_19_14_1_18_1_5280 52 96
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 96 189 3 17 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 96 189
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 50 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 96 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 189 3 16 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 189 (Polychromatic418967fa.accept_14_5_12_7_1_2767
  47 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 189
  (Polychromatic418967fa.accept_15_1_6_9_1_254 46 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 96 189 3 15 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 96 189 (Polychromatic418967fa.accept_14_2_12_7_1_617 44 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 43 96 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 189 3 14 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 189
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 41 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 96 189 (Polychromatic418967fa.accept_19_2_1_18_1_2660 40 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 189 3 13 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 38
  96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 189
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 189 3 12 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 189 (Polychromatic418967fa.accept_15_4_6_9_1_2269 34 96 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 96 189 3 11 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 96 189
  (Polychromatic418967fa.accept_18_14_6_9_1_1950 32 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 96 189 (Polychromatic418967fa.accept_15_1_6_9_1_254 31 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 189 3 10 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 189 (Polychromatic418967fa.accept_15_14_6_9_1_2274
  29 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 189
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 96 189 3 9 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 96 189 (Polychromatic418967fa.accept_15_11_6_9_1_3236 26 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 96 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 189 3 8 32 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 189
  (Polychromatic418967fa.accept_10_3_6_9_1_779 23 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 96 189 (Polychromatic418967fa.accept_23_22_4_5_1_10884 22 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 189 3 7 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 189 (Polychromatic418967fa.accept_17_3_11_2_1_8435 20 96 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 189
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 19 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 96 189 3 6 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 96 189 (Polychromatic418967fa.accept_19_17_1_18_1_2693 17 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 96 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 96 189 3 5 32 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 189
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 96 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 189 3 4 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 96 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 189
  (Polychromatic418967fa.accept_20_10_16_9_1_10927 10 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 96 189 3 3 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 96 189 (Polychromatic418967fa.accept_17_8_11_2_1_3415 8 96 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 189 (Polychromatic418967fa.accept_18_7_6_9_1_4205 7
  96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 189 3 2 32 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 189
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 96 189 (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 96 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 189 3 1 32 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 189 (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 96 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 189
  (Polychromatic418967fa.accept_15_1_6_9_1_254 1 96 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 95 189 (allA_succ_of_accept 94 95 189 (accept_3_4 94 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 95 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 93 95 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 95 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 189 (accept_3_4 91 95 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 90
  95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 189
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 89 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 189 (accept_3_4 88 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 87 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 189 (accept_3_4 85 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 84 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 189
  (Polychromatic418967fa.accept_16_3_15_13_1_2825 83 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 189 (accept_3_4 82 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 189 (accept_3_4 79 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 189
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 77 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 189 (accept_3_4 76 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 189 (accept_3_4 73 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 189 (Polychromatic418967fa.accept_15_12_5_9_1_3234 72 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 71 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 189 (accept_3_4 70 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 189 (Polychromatic418967fa.accept_18_15_5_9_1_5529 69 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 189 (accept_3_4 67 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 189
  (Polychromatic418967fa.accept_20_5_15_9_1_9446 65 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 189 (accept_3_4 64 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 189 (accept_3_4 61 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 189 (Polychromatic418967fa.accept_14_4_11_7_1_1234 60 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 189
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 59 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 189 (accept_3_4 58 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 189 (Polychromatic418967fa.accept_15_12_5_9_1_3234 57 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 189 (accept_3_4 55 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 189
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 53 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 189 (accept_3_4 52 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 189 (accept_3_4 49 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 189
  (Polychromatic418967fa.accept_34_13_27_19_1_10926 47 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 95 189 (accept_3_4 46 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 95 189 (Polychromatic418967fa.accept_13_6_4_7_1_2464 45 95 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 95 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 189 (accept_3_4 43 95 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 189 (accept_3_4 40 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 189 (accept_3_4 37 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 189
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 35 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 189 (accept_3_4 34 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 189 (accept_3_4 31 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 189
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 189 (accept_3_4 28 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 189 (accept_3_4 25 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 189
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 189 (accept_3_4 22 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 189 (accept_3_4 19 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 189
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 189 (accept_3_4 16 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 189 (accept_3_4 13 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 189 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 189 (accept_3_4 10 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 189 (accept_3_4 7 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 189
  (Polychromatic418967fa.accept_20_5_15_9_1_9446 5 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 189 (accept_3_4 4 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 95 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 95 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 189 (accept_3_4 1 95 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 95
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 189
  (allA_succ_of_accept 93 94 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 93 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 189 (accept_3_5 92 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  90 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 189 (accept_3_5 89
  94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 88 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 189 (accept_3_5 86 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 189 (Polychromatic418967fa.accept_18_12_4_9_1_5452
  84 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 189 (accept_3_5 83
  94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 189
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 82 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 94 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 81 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 94 189 (accept_3_5 80 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 94 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  78 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 189 (accept_3_5 77
  94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 189
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 76 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 189 (accept_3_5 74 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 94 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 189 (Polychromatic418967fa.accept_15_12_4_9_1_3204
  72 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 189 (accept_3_5 71
  94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 189
  (Polychromatic418967fa.accept_11_4_6_2_1_51 70 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 94 189 (Polychromatic418967fa.accept_13_4_3_7_1_2515 69 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 189 (accept_3_5 68 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  66 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 189 (accept_3_5 65
  94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 189
  (Polychromatic418967fa.accept_20_4_14_9_1_10822 64 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 189 (accept_3_5 62 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 94 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455
  60 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 189 (accept_3_5 59
  94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 94 189 (Polychromatic418967fa.accept_15_12_4_9_1_3204 57 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 94 189 (accept_3_5 56 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  54 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 189 (accept_3_5 53
  94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 189
  (Polychromatic418967fa.accept_25_2_19_14_1_10925 52 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 189 (accept_3_5 50 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 94 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 94 189 (accept_3_5 47 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  94 189 (Polychromatic418967fa.accept_14_4_10_7_1_1946 46 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 94 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 189 (accept_3_5 44 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 189 (accept_3_5 41 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 189 (Polychromatic418967fa.accept_13_1_3_7_1_1710 40 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 189 (accept_3_5 38 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 94 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 189
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 189 (accept_3_5 35 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455 34 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 189 (accept_3_5 32 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 189 (accept_3_5 29 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 189 (accept_3_5 26 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 94 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 189
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 189 (accept_3_5 23 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 189 (Polychromatic418967fa.accept_13_9_3_7_1_1065 22 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 189 (accept_3_5 20 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 189 (accept_3_5 17 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 189 (Polychromatic418967fa.accept_22_16_6_13_1_6000 16 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 189 (accept_3_5 14 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 94 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 189
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 12 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 189 (accept_3_5 11 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 189 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 189 (accept_3_5 8 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 189 (accept_3_5 5 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  189 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 94 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 94 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 189 (accept_3_5 2 94 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 94 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 189
  (allA_succ_of_accept 92 93 189 (Polychromatic418967fa.accept_18_2_3_9_1_1996 92 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 189 (Polychromatic418967fa.accept_18_1_3_9_1_328 91 93 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 189 3 30 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 189
  (Polychromatic418967fa.accept_14_5_9_7_1_590 89 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 189 (Polychromatic418967fa.accept_15_13_3_9_1_1482 88 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 189 3 29 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  86 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 85 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 189 3 28 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 83 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 189 (Polychromatic418967fa.accept_14_12_9_7_1_2762 82 93
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 189 3 27 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 189
  (Polychromatic418967fa.accept_15_5_3_9_1_283 80 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 189 (Polychromatic418967fa.accept_17_11_8_2_1_3398 79 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 189 3 26 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 189 (Polychromatic418967fa.accept_19_1_17_18_1_8101
  77 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 189
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 76 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 189 3 25 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 74 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 73 93 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 189 3 24 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 189
  (Polychromatic418967fa.accept_25_21_18_14_1_7190 71 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 93 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 70 93 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 189 3 23 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 189
  (Polychromatic418967fa.accept_14_12_9_7_1_2762 68 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 189 (Polychromatic418967fa.accept_17_16_8_2_1_5890 67 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 93 189 3 22 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 93 189 (Polychromatic418967fa.accept_15_5_3_9_1_283 65
  93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 189
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 64 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 93 189 3 21 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 93 189 (Polychromatic418967fa.accept_17_11_8_2_1_3398 62 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 189 (Polychromatic418967fa.accept_13_9_2_7_1_1083 61 93 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 189 3 20 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 189
  (Polychromatic418967fa.accept_20_19_13_9_1_5019 59 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 93 189 (Polychromatic418967fa.accept_14_2_9_7_1_5633 58 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 93 189 3 19 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 93 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  56 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 189
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 55 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 93 189 3 18 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 93 189 (Polychromatic418967fa.accept_15_8_3_9_1_4220 53 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 93 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 189 3 17 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 189
  (Polychromatic418967fa.accept_15_5_3_9_1_283 50 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 189 (Polychromatic418967fa.accept_18_13_3_9_1_4233 49 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 93 189 3 16 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 93 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452
  47 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 189
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 46 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 93 189 3 15 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 93 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 189 (Polychromatic418967fa.accept_15_13_3_9_1_1482 43 93
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 189 3 14 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 189 (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 189 3 13 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 189 (Polychromatic418967fa.accept_15_8_3_9_1_4220
  38 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 189
  (Polychromatic418967fa.accept_18_1_3_9_1_328 37 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 93 189 3 12 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 93 189 (Polychromatic418967fa.accept_13_9_2_7_1_1083 35 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 34 93 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 189 3 11 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 189
  (Polychromatic418967fa.accept_18_14_3_9_1_4234 32 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 31 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 189 3 10 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 189
  (Polychromatic418967fa.accept_19_10_17_18_1_9555 29 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 93 189 (Polychromatic418967fa.accept_15_13_3_9_1_1482 28 93 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 189 3 9 31 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 189
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 189 (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 189 3 8 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 189 (Polychromatic418967fa.accept_15_8_3_9_1_4220 23 93 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 189
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 22 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 189 3 7 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 189 (Polychromatic418967fa.accept_15_5_3_9_1_283 20 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 93 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 189 3 6 31 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 189
  (Polychromatic418967fa.accept_28_17_9_21_1_10924 17 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 93 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 93 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 189 3 5 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262
  14 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 189
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 189 3 4 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 189 (Polychromatic418967fa.accept_17_11_8_2_1_3398 11 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 189 (Polychromatic418967fa.accept_15_10_3_9_1_3285 10 93
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 189 3 3 31 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 189 (Polychromatic418967fa.accept_18_7_3_9_1_1020 7 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 189 3 2 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 93 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 189
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 93 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 189 3 1 31 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 189 (Polychromatic418967fa.accept_14_2_9_7_1_5633 2 93 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 189 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 93 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 189
  (allA_succ_of_accept 91 92 189 (accept_3_4 91 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 90 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 189 (accept_3_4 88 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 87 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 86 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 189 (accept_3_4 85 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 189 (Polychromatic418967fa.accept_13_6_1_7_1_1690 84 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 189 (accept_3_4 82 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 189
  (Polychromatic418967fa.accept_17_12_7_2_1_4561 80 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 189 (accept_3_4 79 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 78 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 189 (accept_3_4 76 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 75 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 189
  (Polychromatic418967fa.accept_16_10_12_13_1_4950 74 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 92 189 (accept_3_4 73 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 92 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 92 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 189 (accept_3_4 70 92 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 189 (Polychromatic418967fa.accept_14_13_8_7_1_1224
  69 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 189
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 68 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 189 (accept_3_4 67 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 189 (accept_3_4 64 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 189
  (Polychromatic418967fa.accept_14_6_8_7_1_589 62 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 189 (accept_3_4 61 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 189 (Polychromatic418967fa.accept_13_8_1_7_1_2505 60 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 189 (accept_3_4 58 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 189
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 56 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 189 (accept_3_4 55 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 189 (accept_3_4 52 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 189
  (Polychromatic418967fa.accept_11_6_4_2_1_599 50 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 189 (accept_3_4 49 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 189 (Polychromatic418967fa.accept_14_6_8_7_1_589 48 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 189 (accept_3_4 46 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 189 (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 189
  (Polychromatic418967fa.accept_26_18_14_7_1_10923 44 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 92 189 (accept_3_4 43 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 92 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 92 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 189 (accept_3_4 40 92 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 189 (Polychromatic418967fa.accept_11_6_4_2_1_599
  39 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 189
  (Polychromatic418967fa.accept_15_8_2_9_1_3200 38 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 189 (accept_3_4 37 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 189 (Polychromatic418967fa.accept_16_4_12_13_1_990 36 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 189 (accept_3_4 34 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 189
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 32 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 189 (accept_3_4 31 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 189 (accept_3_4 28 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 189
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 26 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 189 (accept_3_4 25 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 189 (accept_3_4 22 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 20 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 189 (accept_3_4 19 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 189 (accept_3_4 16 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 189 (Polychromatic418967fa.accept_14_1_8_7_1_1253 15 92 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 189
  (Polychromatic418967fa.accept_19_14_16_18_1_9534 14 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 92 189 (accept_3_4 13 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 92 189 (Polychromatic418967fa.accept_17_12_7_2_1_4561 12 92 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 189 (accept_3_4 10 92 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 92
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 189
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 189 (accept_3_4 7 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  189 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 189 (accept_3_4 4 92 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 92 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 189
  (Polychromatic418967fa.accept_19_2_16_18_1_10922 2 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 92 189 (accept_3_4 1 92 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 189
  (allA_succ_of_accept 90 91 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 189 (accept_3_5 89 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  87 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 189 (accept_3_5 86
  91 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 85 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 91 189 7 12 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 91 189 (accept_3_5 83 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 189 (Polychromatic418967fa.accept_15_6_1_9_1_1476 81 91 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 189 (accept_3_5 80 91 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 189 (Polychromatic418967fa.accept_19_3_15_18_1_2682 79 91 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 91 189 7 11 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 76 91 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 75 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 189 (accept_3_5 74 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 189
  (Polychromatic418967fa.accept_19_16_15_18_1_5252 73 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 91 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 189 (accept_3_5 71 91 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 91 189 7 10 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 91 189 (Polychromatic418967fa.accept_17_1_6_2_1_623 69 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 189 (accept_3_5 68 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090
  67 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 189 (accept_3_5 65 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 91 189 7 9 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 91 189 (accept_3_5 62 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 91 189 (Polychromatic418967fa.accept_19_4_15_18_1_10821 61 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 189 (Polychromatic418967fa.accept_18_6_1_9_1_5551 60 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 189 (accept_3_5 59 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 189
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 57 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 91 189 7 8 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 91 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 55 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 189 (accept_3_5 53 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52
  91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 189 (accept_3_5 50 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 91
  189 7 7 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  91 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 91 189 (accept_3_5 47 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 91 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 189 (accept_3_5 44 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 189
  (Polychromatic418967fa.accept_25_18_16_14_1_10921 43 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 91 189 7 6 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 91 189 (accept_3_5 41 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 91 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 189 (accept_3_5 38 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500
  37 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 189
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 91 189 7 5 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 91 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 189 (Polychromatic418967fa.accept_19_14_15_18_1_5250 33 91
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 189 (accept_3_5 32 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 189
  (Polychromatic418967fa.accept_19_12_15_18_1_9544 31 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 189 (accept_3_5 29 91 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 91 189 7 4 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 91 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 91 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 189 (accept_3_5 26 91 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 189
  (Polychromatic418967fa.accept_16_8_11_13_1_7265 24 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 189 (accept_3_5 23 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 91 189 7 3 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 91 189 (accept_3_5 20 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 91 189 (Polychromatic418967fa.accept_26_19_13_7_1_10920 19 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 189 (accept_3_5 17 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 91 189 7 2 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 91 189 (Polychromatic418967fa.accept_17_13_6_2_1_5850 13 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 189 (accept_3_5 11 91 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 189
  (Polychromatic418967fa.accept_19_9_15_18_1_10919 9 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 189 (accept_3_5 8 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 189
  7 1 13 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 91
  189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 189 (accept_3_5 5 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 189 (accept_3_5 2 91 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 91 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 189
  (allA_succ_of_accept 89 90 189 (Polychromatic418967fa.accept_13_11_12_7_1_2443 89 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 88 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 189 3 29 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 86 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 90 189 (Polychromatic418967fa.accept_14_1_6_7_1_1936 85 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 189 3 28 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 83
  90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 82 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 90 189 9 9 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 90 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 80 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 189 3 26 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 189
  (Polychromatic418967fa.accept_19_1_14_18_1_3919 77 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 76 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 189 3 25 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 74
  90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 189
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 73 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 189 9 8 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 70 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 90 189 3 23 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 68 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 189 3 22 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 189 (Polychromatic418967fa.accept_17_14_5_2_1_4559
  65 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 64 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 90 189 9 7 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 90 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 62 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 189 (Polychromatic418967fa.accept_19_4_14_18_1_5234 61 90
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 189 3 20 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 90 189 3 19 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 90 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  56 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 189 9 6 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 189 (Polychromatic418967fa.accept_16_5_10_13_1_6042 53 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 52 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 90 189 3 17 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 90 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 50 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 189 (Polychromatic418967fa.accept_13_10_12_7_1_1079 49 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 189 3 16 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 189 9 5 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 189 3 14 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 189
  (Polychromatic418967fa.accept_14_13_6_7_1_2013 41 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 90 189 3 13 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 38
  90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 189
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 189 9 4 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 189 3 11 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 189 3 10 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 189 (Polychromatic418967fa.accept_14_1_6_7_1_1936
  29 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 90 189 9 3 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 90 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 189 (Polychromatic418967fa.accept_20_5_10_9_1_9485 25 90
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 189 3 8 30 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 189 3 7 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 189 9 2 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 189 (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 189 3 5 30 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 189 (Polychromatic418967fa.accept_14_13_6_7_1_2013 13 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 189 3 4 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 90 189 9 1 10 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 189 3 2 30 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 189
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 90 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 189 3 1 30 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 90 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 189
  (Polychromatic418967fa.accept_14_1_6_7_1_1936 1 90 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 189 (allA_succ_of_accept 88 89 189 (accept_3_4 88 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 87 89 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 89 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 189 (accept_3_4 85 89 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 84
  89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 189
  (Polychromatic418967fa.accept_13_5_11_7_1_559 83 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 189 (accept_3_4 82 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 189 (Polychromatic418967fa.accept_13_3_11_7_1_2488 81 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 189 (accept_3_4 79 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 189 (Polychromatic418967fa.accept_22_12_1_13_1_1623 78 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 189
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 77 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 189 (accept_3_4 76 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 189 (accept_3_4 73 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 189 (Polychromatic418967fa.accept_14_2_5_7_1_3767 72 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 189
  (Polychromatic418967fa.accept_16_7_9_13_1_4948 71 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 189 (accept_3_4 70 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 189 (accept_3_4 67 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 189 (Polychromatic418967fa.accept_13_1_11_7_1_1704 66 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 189
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 65 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 189 (accept_3_4 64 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 189 (accept_3_4 61 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 189
  (Polychromatic418967fa.accept_23_13_20_5_1_9197 59 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 189 (accept_3_4 58 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 189 (Polychromatic418967fa.accept_13_5_11_7_1_559 57 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 189 (accept_3_4 55 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 189
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 53 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 189 (accept_3_4 52 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 189 (accept_3_4 49 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 189 (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 189
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 47 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 189 (accept_3_4 46 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 189 (Polychromatic418967fa.accept_26_19_11_7_1_9029 45 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 189 (accept_3_4 43 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 189 (Polychromatic418967fa.accept_13_3_11_7_1_2488 42 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 189
  (Polychromatic418967fa.accept_28_13_5_21_1_10918 41 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 89 189 (accept_3_4 40 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 89 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 89 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 89 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 189 (accept_3_4 37 89 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 36
  89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 189
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 35 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 189 (accept_3_4 34 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 189 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 189 (accept_3_4 31 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 189 (Polychromatic418967fa.accept_13_4_11_7_1_558 30 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 189
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 29 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 189 (accept_3_4 28 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 189 (accept_3_4 25 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 189 (Polychromatic418967fa.accept_19_5_13_18_1_5249 24 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 189
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 23 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 189 (accept_3_4 22 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 189 (accept_3_4 19 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 189 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 189
  (Polychromatic418967fa.accept_13_4_11_7_1_558 17 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 189 (accept_3_4 16 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 189 (accept_3_4 13 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 189
  (Polychromatic418967fa.accept_32_11_25_29_1_10917 11 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 89 189 (accept_3_4 10 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 89 189 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 89 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 189 (accept_3_4 7 89 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471
  6 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 189
  (Polychromatic418967fa.accept_13_5_11_7_1_559 5 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 189 (accept_3_4 4 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 89 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 189 (accept_3_4 1 89 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 189
  (allA_succ_of_accept 87 88 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 87 88 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 189 (accept_3_5 86 88 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 189 (Polychromatic418967fa.accept_10_4_8_9_1_784
  84 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 189 (accept_3_5 83
  88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 189
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 82 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 88 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 81 88 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 189 (accept_3_5 80 88 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 189 (Polychromatic418967fa.accept_12_6_4_9_1_544
  78 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 189 (accept_3_5 77
  88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 189
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 76 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 88 189 (Polychromatic418967fa.accept_16_11_8_13_1_3844 75 88 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 189 (accept_3_5 74 88 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 189
  (Polychromatic418967fa.accept_19_15_12_18_1_6634 72 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 88 189 (accept_3_5 71 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 88 189 (Polychromatic418967fa.accept_19_13_12_18_1_2677 70 88 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 69 88
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 189 (accept_3_5 68 88 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 67
  88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 66 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 189 (accept_3_5 65 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 189 (Polychromatic418967fa.accept_15_3_13_9_1_3196 63 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 189 (accept_3_5 62 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 189
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 60 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 189 (accept_3_5 59 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 189 (Polychromatic418967fa.accept_19_1_12_18_1_10820 58 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 57 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 189 (accept_3_5 56 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 54 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 189 (accept_3_5 53 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 189 (Polychromatic418967fa.accept_14_10_4_7_1_1214 52 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 189 (accept_3_5 50 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 189
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 48 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 189 (accept_3_5 47 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 189 (Polychromatic418967fa.accept_24_22_16_21_1_10916 46 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 189 (Polychromatic418967fa.accept_14_3_4_7_1_175 45 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 189 (accept_3_5 44 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 189 (accept_3_5 41 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 189 (Polychromatic418967fa.accept_25_15_13_14_1_10915 40 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 189 (Polychromatic418967fa.accept_14_11_4_7_1_609 39 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 189 (accept_3_5 38 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 189
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 189 (accept_3_5 35 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 189 (Polychromatic418967fa.accept_15_3_13_9_1_3196 33 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 189 (accept_3_5 32 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 189 (accept_3_5 29 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 189 (Polychromatic418967fa.accept_16_12_8_13_1_6073 28 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 189 (accept_3_5 26 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 189 (accept_3_5 23 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 189 (Polychromatic418967fa.accept_15_7_13_9_1_1466 22 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 189 (accept_3_5 20 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 189 (accept_3_5 17 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 189 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 189 (Polychromatic418967fa.accept_18_15_16_9_1_4299 15 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 189 (accept_3_5 14 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 189
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 189 (accept_3_5 11 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 189 (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 189 (Polychromatic418967fa.accept_19_9_12_18_1_8099 9 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 189 (accept_3_5 8 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 189 (accept_3_5 5 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  189 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 88 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 189 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 88 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 189 (accept_3_5 2 88 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 189
  (allA_succ_of_accept 86 87 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 85 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 189 3 28 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 83 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 189 3 27 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 189 (Polychromatic418967fa.accept_13_2_9_7_1_164 80
  87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 79 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 189 3 26 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 189 (Polychromatic418967fa.accept_13_11_9_7_1_2484 76 87
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 189 3 25 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 73 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 189 3 24 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  71 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 189 3 23 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 68 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 67 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 189 3 22 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 65 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 189 (Polychromatic418967fa.accept_15_4_12_9_1_773 64 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 189 3 21 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 61 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 189 3 20 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 189 3 19 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 56 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 189 3 18 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 53
  87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 189
  (Polychromatic418967fa.accept_10_2_7_9_1_783 52 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 189 3 17 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 189 3 16 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 189 3 15 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 189 (Polychromatic418967fa.accept_15_14_12_9_1_3216
  44 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 189 3 14 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 189 (Polychromatic418967fa.accept_15_10_12_9_1_776 40 87
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 189 3 13 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 189 3 12 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 189 3 11 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 189 3 10 29 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 28 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 189 3 9 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 189 3 8 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 189 3 7 29 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 189
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 20 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 189 3 6 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 189
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 189 3 5 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 189 3 4 29 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 189 3 3 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 189 3 2 29 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 87 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 189 3 1 29 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 87 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 189
  (allA_succ_of_accept 85 86 189 (accept_3_4 85 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 84 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 189 (accept_3_4 82 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 81 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 189
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 80 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 189 (accept_3_4 79 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 78 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 189 (accept_3_4 76 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 189
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 74 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 189 (accept_3_4 73 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 189 (Polychromatic418967fa.accept_22_6_20_13_1_10914 72 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 189 (accept_3_4 70 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 189 (Polychromatic418967fa.accept_34_1_18_19_1_10913 69 86 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 189
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 68 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 189 (accept_3_4 67 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 189 (accept_3_4 64 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 189
  (Polychromatic418967fa.accept_11_7_9_2_1_260 62 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 189 (accept_3_4 61 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 189 (Polychromatic418967fa.accept_18_6_14_9_1_3039 60 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 189 (accept_3_4 58 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 189 (Polychromatic418967fa.accept_16_9_6_13_1_3831 57 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 189
  (Polychromatic418967fa.accept_23_10_17_5_1_5790 56 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 189 (accept_3_4 55 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 189 (accept_3_4 52 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 189
  (Polychromatic418967fa.accept_15_5_11_9_1_4276 50 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 189 (accept_3_4 49 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 189 (accept_3_4 46 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 189
  (Polychromatic418967fa.accept_31_13_24_3_1_10912 44 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 86 189 (accept_3_4 43 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 86 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 86 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 86 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 86 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 189 (accept_3_4 40 86 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 189
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 38 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 189 (accept_3_4 37 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 189 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 189 (accept_3_4 34 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 189
  (Polychromatic418967fa.accept_15_2_11_9_1_263 32 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 189 (accept_3_4 31 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 189 (accept_3_4 28 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 189
  (Polychromatic418967fa.accept_11_4_9_2_1_259 26 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 189 (accept_3_4 25 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 189 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 189 (accept_3_4 22 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 189 (Polychromatic418967fa.accept_15_6_11_9_1_3215 21 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 189
  (Polychromatic418967fa.accept_15_5_11_9_1_4276 20 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 189 (accept_3_4 19 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 189 (accept_3_4 16 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 189
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 14 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 189 (accept_3_4 13 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 189 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 189 (accept_3_4 10 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 189 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 86 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 189
  (Polychromatic418967fa.accept_19_8_10_18_1_5232 8 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 189 (accept_3_4 7 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 189 (accept_3_4 4 86 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 189 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2
  86 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 189 (accept_3_4 1 86 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 189
  (allA_succ_of_accept 84 85 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 84 85 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 189 (accept_3_5 83 85 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 189 (Polychromatic418967fa.accept_10_1_5_9_1_157
  81 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 189 (accept_3_5 80
  85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 189
  (Polychromatic418967fa.accept_15_4_10_9_1_4298 79 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 189 (Polychromatic418967fa.accept_14_8_1_7_1_3725 78 85 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 189 (accept_3_5 77 85 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 189 (Polychromatic418967fa.accept_12_3_1_9_1_202
  75 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 189 (accept_3_5 74
  85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 189
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 73 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 85 189 (Polychromatic418967fa.accept_15_12_10_9_1_798 72 85 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 189 (accept_3_5 71 85 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 189 (Polychromatic418967fa.accept_14_13_1_7_1_1211
  69 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 189 (accept_3_5 68
  85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 189
  (Polychromatic418967fa.accept_19_10_9_18_1_10911 67 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 85 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 66 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 189 (accept_3_5 65 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 63 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 85 189 (accept_3_5 62 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  85 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 85 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 189 (accept_3_5 59 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 189
  (Polychromatic418967fa.accept_15_12_10_9_1_798 57 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 189 (accept_3_5 56 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  85 189 (Polychromatic418967fa.accept_14_13_1_7_1_1211 55 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 85 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 189 (accept_3_5 53 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 51 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 189 (accept_3_5 50 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 189 (Polychromatic418967fa.accept_14_6_1_7_1_2775 48 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 189 (accept_3_5 47 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 189
  (Polychromatic418967fa.accept_25_20_10_14_1_10910 45 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 85 189 (accept_3_5 44 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 85 189 (Polychromatic418967fa.accept_19_5_9_18_1_10839 43 85 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 189 (Polychromatic418967fa.accept_15_12_10_9_1_798 42 85
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 189 (accept_3_5 41 85 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40
  85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 189 (accept_3_5 38 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 189 (Polychromatic418967fa.accept_25_12_10_14_1_10909 37 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 189 (accept_3_5 35 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 189
  (Polychromatic418967fa.accept_15_3_10_9_1_769 33 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 189 (accept_3_5 32 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 189 (Polychromatic418967fa.accept_20_10_5_9_1_10908 30 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 189 (accept_3_5 29 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 189
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 189 (accept_3_5 26 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 189 (Polychromatic418967fa.accept_16_9_5_13_1_4972 25 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 189 (accept_3_5 23 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 189 (accept_3_5 20 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 189 (Polychromatic418967fa.accept_15_4_10_9_1_4298 19 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 189 (Polychromatic418967fa.accept_15_3_10_9_1_769 18 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 189 (accept_3_5 17 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 189 (accept_3_5 14 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 189 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 189 (Polychromatic418967fa.accept_15_12_10_9_1_798 12 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 189 (accept_3_5 11 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 85 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 189
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 189 (accept_3_5 8 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  189 (Polychromatic418967fa.accept_20_7_5_9_1_10833 7 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 85 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 189 (accept_3_5 5 85 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 189 (accept_3_5 2 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  189 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 85 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 85 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84
  189 (allA_succ_of_accept 83 84 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 83 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 82 84 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 189 3 27 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 189
  (Polychromatic418967fa.accept_19_4_8_18_1_5268 80 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 79 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 189 3 26 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 84 189 7 11 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 84 189 (Polychromatic418967fa.accept_16_12_4_13_1_3827
  76 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 84 189 3 25 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 84 189
  (Polychromatic418967fa.accept_13_9_6_7_1_551 74 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 84 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 189 3 24 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 189 (Polychromatic418967fa.accept_16_7_4_13_1_1057
  71 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 189 7 10 12 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 84 189 3 23 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 68 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 84 189 (Polychromatic418967fa.accept_19_10_8_18_1_2669 67 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 189 3 22 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 65
  84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 189
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 84 189 21 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 84 189 (Polychromatic418967fa.accept_20_2_4_9_1_9524 62 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 61 84 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 189 3 20 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 189
  (Polychromatic418967fa.accept_17_8_16_2_1_10847 59 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 84 189 3 19 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 84 189 7 8 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 55
  84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 189 3 18 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 189
  (Polychromatic418967fa.accept_10_3_4_9_1_15 53 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 189 (Polychromatic418967fa.accept_17_1_16_2_1_1404 52 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 189 3 17 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 189
  (Polychromatic418967fa.accept_22_6_18_13_1_10907 50 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 49 84 189 7 7 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 84 189 3 16 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 84 189 (Polychromatic418967fa.accept_18_11_12_9_1_992 47 84 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 189
  (Polychromatic418967fa.accept_18_10_12_9_1_2012 46 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 84 189 3 15 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 84 189 (Polychromatic418967fa.accept_16_12_4_13_1_3827 44 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 43 84 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 189 21 2 4 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 40 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 84 189 3 13 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 84 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  38 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 189
  (Polychromatic418967fa.accept_23_14_15_5_1_10906 37 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 84 189 3 12 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 84 189 7 5 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 84 189 (Polychromatic418967fa.accept_18_16_12_9_1_5504 34 84 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 189 3 11 28 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 189
  (Polychromatic418967fa.accept_19_13_8_18_1_10905 32 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 84 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 84 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 189 3 10 28 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 189
  (Polychromatic418967fa.accept_18_11_12_9_1_992 29 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 189 7 4 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 84 189 3 9 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 84 189 (Polychromatic418967fa.accept_19_7_8_18_1_1576 26 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 189 3 8 28 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 189
  (Polychromatic418967fa.accept_10_3_4_9_1_15 23 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 22 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 189 21 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 84 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 189
  (Polychromatic418967fa.accept_20_19_4_9_1_5025 19 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 189 3 6 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 189 (Polychromatic418967fa.accept_18_16_12_9_1_5504 16 84
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 189 3 5 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 189 7 2 12 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 189
  (Polychromatic418967fa.accept_10_3_4_9_1_15 13 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 189 3 4 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 189 (Polychromatic418967fa.accept_18_11_12_9_1_992 11 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 189 (Polychromatic418967fa.accept_18_10_12_9_1_2012 10 84
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 189 3 3 28 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 84 189 7 1 12 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 84 189 3 2 28 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 84 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 189 3 1 28 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 189
  (Polychromatic418967fa.accept_20_2_4_9_1_9524 2 84 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 84 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 189
  (allA_succ_of_accept 82 83 189 (accept_3_4 82 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 81 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 189 (accept_3_4 79 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 189
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 77 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 189 (accept_3_4 76 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 75 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 189 (accept_3_4 73 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 189 (Polychromatic418967fa.accept_16_8_3_13_1_7295 72 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 189
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 71 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 189 (accept_3_4 70 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 189 (Polychromatic418967fa.accept_18_15_11_9_1_4256 69 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 189 (accept_3_4 67 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 189
  (Polychromatic418967fa.accept_16_1_3_13_1_2785 65 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 189 (accept_3_4 64 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 189 (accept_3_4 61 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 189 (Polychromatic418967fa.accept_24_12_11_21_1_7280 60 83 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 189
  (Polychromatic418967fa.accept_11_4_6_2_1_51 59 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 189 (accept_3_4 58 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 189 (Polychromatic418967fa.accept_14_1_13_7_1_1205 57 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 189 (accept_3_4 55 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 189
  (Polychromatic418967fa.accept_19_15_7_18_1_9532 53 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 189 (accept_3_4 52 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 189 (accept_3_4 49 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 48 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 189
  (Polychromatic418967fa.accept_15_2_8_9_1_4294 47 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 189 (accept_3_4 46 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 189 (Polychromatic418967fa.accept_23_22_14_5_1_10904 45 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 189 (accept_3_4 43 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 189
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 41 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 189 (accept_3_4 40 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 189 (accept_3_4 37 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 189
  (Polychromatic418967fa.accept_20_15_3_9_1_5007 35 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 189 (accept_3_4 34 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 189 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 189 (accept_3_4 31 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 189
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 189 (accept_3_4 28 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 189 (accept_3_4 25 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 189
  (Polychromatic418967fa.accept_25_23_8_14_1_10903 23 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 83 189 (accept_3_4 22 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 83 189 (Polychromatic418967fa.accept_17_4_15_2_1_4551 21 83 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 189 (accept_3_4 19 83 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 189
  (Polychromatic418967fa.accept_15_2_8_9_1_4294 17 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 189 (accept_3_4 16 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 189 (accept_3_4 13 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 189 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 189
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 189 (accept_3_4 10 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 189 (Polychromatic418967fa.accept_23_9_14_5_1_10814 9 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 189 (accept_3_4 7 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 189
  (Polychromatic418967fa.accept_28_5_27_21_1_8831 5 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 189 (accept_3_4 4 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 83 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 189 (accept_3_4 1 83 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 189
  (allA_succ_of_accept 81 82 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 81 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 189 (accept_3_5 80 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  78 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 189 (accept_3_5 77
  82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 189
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 76 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 189 (accept_3_5 74 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 82 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 189 (Polychromatic418967fa.accept_14_2_12_7_1_617
  72 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 189 (accept_3_5 71
  82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 189
  (Polychromatic418967fa.accept_25_20_7_14_1_9097 70 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 82 189 (Polychromatic418967fa.accept_16_5_2_13_1_1007 69 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 189 (accept_3_5 68 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  66 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 189 (accept_3_5 65
  82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 189
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 64 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 189 (accept_3_5 62 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 82 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 189 (Polychromatic418967fa.accept_19_3_6_18_1_2665
  60 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 189 (accept_3_5 59
  82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 189
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 58 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 82 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 189 (accept_3_5 56 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  54 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 189 (accept_3_5 53
  82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 189 (accept_3_5 50 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 82 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694
  48 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 189 (accept_3_5 47
  82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 189
  (Polychromatic418967fa.accept_15_1_7_9_1_20 46 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 82 189 (Polychromatic418967fa.accept_13_6_4_7_1_2464 45 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 189 (accept_3_5 44 82 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  42 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 189 (accept_3_5 41
  82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 189
  (Polychromatic418967fa.accept_22_18_16_13_1_10902 40 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 189 (accept_3_5 38 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 82 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 189
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 189 (accept_3_5 35 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 189 (Polychromatic418967fa.accept_25_9_7_14_1_10901 34 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 189 (Polychromatic418967fa.accept_14_5_12_7_1_2767 33 82 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 189 (accept_3_5 32 82 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 189 (accept_3_5 29 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 189 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 189 (accept_3_5 26 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 82 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 189
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 189 (accept_3_5 23 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 22 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 189 (accept_3_5 20 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 189 (accept_3_5 17 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 189 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 189 (accept_3_5 14 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 189
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 189 (accept_3_5 11 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 189 (Polychromatic418967fa.accept_13_10_4_7_1_2465 10 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 189 (accept_3_5 8 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 189 (accept_3_5 5 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  189 (Polychromatic418967fa.accept_20_4_2_9_1_1261 4 82 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 82 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 189 (accept_3_5 2 82 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 189
  (allA_succ_of_accept 80 81 189 (Polychromatic418967fa.accept_14_10_11_7_1_1955 80 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 189 (Polychromatic418967fa.accept_13_1_3_7_1_1710 79 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 189 3 26 27 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 189
  (Polychromatic418967fa.accept_19_1_5_18_1_8109 77 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 76 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 189 3 25 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 189 (Polychromatic418967fa.accept_13_9_3_7_1_1065
  74 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 189
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 73 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 189 9 8 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 189 (Polychromatic418967fa.accept_15_11_6_9_1_3236 71 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 189 (Polychromatic418967fa.accept_19_13_5_18_1_8106 70 81
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 189 3 23 27 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 68 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 189 (Polychromatic418967fa.accept_16_3_1_13_1_4968 67 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 189 3 22 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 65
  81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 64 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 189 9 7 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 62 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 61 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 189 3 20 27 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 189
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 59 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 58 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 189 3 19 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 189 (Polychromatic418967fa.accept_13_4_3_7_1_2515
  56 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 55 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 189 27 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 53 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 189 3 17 27 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 189
  (Polychromatic418967fa.accept_11_6_4_2_1_599 50 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 189 3 16 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455
  47 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 189
  (Polychromatic418967fa.accept_14_4_11_7_1_1234 46 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 189 9 5 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 189 (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 189 3 14 27 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 189
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 41 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 189 (Polychromatic418967fa.accept_13_1_3_7_1_1710 40 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 189 3 13 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 38
  81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 189
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 189 9 4 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455 34 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 189 3 11 27 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 189
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 189 3 10 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 189 (Polychromatic418967fa.accept_15_14_6_9_1_2274
  29 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 189 27 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 189 (Polychromatic418967fa.accept_15_11_6_9_1_3236 26 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 189 3 8 27 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 189
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 22 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 189 3 7 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 189
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 189 9 2 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 189 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 189 3 5 27 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 189
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 189 (Polychromatic418967fa.accept_19_13_5_18_1_8106 13 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 189 3 4 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 189 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 189
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 189 9 1 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 189 (Polychromatic418967fa.accept_17_7_13_2_1_10840 7 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 189 3 2 27 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 81 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 189 3 1 27 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 81 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 189
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 81 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 189
  (allA_succ_of_accept 79 80 189 (accept_3_4 79 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 78 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 189 (accept_3_4 76 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 189 (Polychromatic418967fa.accept_17_7_12_2_1_7105 75 80 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 189
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 74 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 189 (accept_3_4 73 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 189 (Polychromatic418967fa.accept_15_12_5_9_1_3234 72 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 189 (accept_3_4 70 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 189 (Polychromatic418967fa.accept_22_3_14_13_1_10900 69 80 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 189
  (Polychromatic418967fa.accept_19_11_4_18_1_5226 68 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 189 (accept_3_4 67 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 189 (accept_3_4 64 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 63 80 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 189
  (Polychromatic418967fa.accept_19_5_4_18_1_5242 62 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 189 (accept_3_4 61 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 60 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 189 (accept_3_4 58 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 57 80 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 189
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 56 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 189 (accept_3_4 55 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 189 (accept_3_4 52 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 189 (Polychromatic418967fa.accept_32_19_16_29_1_10899 51 80 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 189
  (Polychromatic418967fa.accept_22_6_14_13_1_10898 50 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 80 189 (accept_3_4 49 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 80 189 (Polychromatic418967fa.accept_13_9_2_7_1_1083 48 80 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 189 (accept_3_4 46 80 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090
  45 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 189
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 44 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 189 (accept_3_4 43 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 189 (accept_3_4 40 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 189 (Polychromatic418967fa.accept_14_11_10_7_1_1948 39 80 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 189
  (Polychromatic418967fa.accept_17_4_12_2_1_2349 38 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 189 (accept_3_4 37 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 189 (Polychromatic418967fa.accept_19_17_4_18_1_6643 36 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 189 (accept_3_4 34 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 80 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 189
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 32 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 189 (accept_3_4 31 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 189 (accept_3_4 28 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 189 (Polychromatic418967fa.accept_15_12_5_9_1_3234 27 80 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 189
  (Polychromatic418967fa.accept_15_11_5_9_1_3205 26 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 189 (accept_3_4 25 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 189 (Polychromatic418967fa.accept_17_7_12_2_1_7105 24 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 189 (accept_3_4 22 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 80 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 189
  (Polychromatic418967fa.accept_24_20_8_21_1_10897 20 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 80 189 (accept_3_4 19 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 80 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 80 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 189 (accept_3_4 16 80 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 189
  (Polychromatic418967fa.accept_19_15_4_18_1_5227 15 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 80 189 (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 80 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 189 (accept_3_4 13 80 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 80 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 189 (accept_3_4 10 80
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 189
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 80 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 8 80 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 189 (accept_3_4 7 80 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 80 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 80 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 80 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 189 (accept_3_4 4 80 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 189 (Polychromatic418967fa.accept_14_3_10_7_1_3773
  3 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 189
  (Polychromatic418967fa.accept_19_2_4_18_1_9556 2 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 80 189 (accept_3_4 1 80 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 189
  (allA_succ_of_accept 78 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 189 (accept_3_5 77 79 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  75 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 189 (accept_3_5 74
  79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 189
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 73 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 189 (Polychromatic418967fa.accept_14_2_9_7_1_5633 72 79 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 189 (accept_3_5 71 79 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 189
  (Polychromatic418967fa.accept_25_19_4_14_1_10896 69 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 79 189 (accept_3_5 68 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 79 189 (Polychromatic418967fa.accept_16_3_15_13_1_2825 67 79 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 189 (accept_3_5 65 79 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 79 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 64
  79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 189 (accept_3_5 62 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 189 (Polychromatic418967fa.accept_14_5_9_7_1_590 61 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 189 (Polychromatic418967fa.accept_13_8_1_7_1_2505 60 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 189 (accept_3_5 59 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 189
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 57 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 189 (accept_3_5 56 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706 55 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 189 (accept_3_5 53 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 189 (accept_3_5 50 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 189 (Polychromatic418967fa.accept_19_11_3_18_1_10828 49 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 189 (Polychromatic418967fa.accept_20_8_19_9_1_6417 48 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 189 (accept_3_5 47 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 189
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 189 (accept_3_5 44 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 189 (Polychromatic418967fa.accept_15_13_4_9_1_2283 43 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 189 (accept_3_5 41 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 189 (accept_3_5 38 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 189 (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 189 (accept_3_5 35 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 189
  (Polychromatic418967fa.accept_14_5_9_7_1_590 33 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 189 (accept_3_5 32 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 189 (Polychromatic418967fa.accept_36_31_7_9_1_10895 31 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 189 (accept_3_5 29 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 189 (accept_3_5 26 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 189 (Polychromatic418967fa.accept_15_10_4_9_1_3203 25 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 189 (accept_3_5 23 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 189
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 189 (accept_3_5 20 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 189 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 189 (accept_3_5 17 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 189 (accept_3_5 14 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 189 (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 189 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 189 (accept_3_5 11 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 189
  (Polychromatic418967fa.accept_17_9_11_2_1_5894 9 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 189 (accept_3_5 8 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  189 (Polychromatic418967fa.accept_23_7_10_5_1_10894 7 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 189 (accept_3_5 5 79 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 189 (accept_3_5 2 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  189 (Polychromatic418967fa.accept_25_1_4_14_1_10893 1 79 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 79 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  78 189 (allA_succ_of_accept 77 78 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 77 78 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624
  76 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 189 3 25 26 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 74 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 189 (Polychromatic418967fa.accept_15_13_3_9_1_1482 73 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 189 3 24 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 70 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 189 3 23 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 68 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 189 3 22 26 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 189
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 65 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 64 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 189 3 21 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 62
  78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 189
  (Polychromatic418967fa.accept_10_1_8_9_1_787 61 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 189 3 20 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 58 78 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 189 3 19 26 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 189 3 18 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 189 (Polychromatic418967fa.accept_15_8_3_9_1_4220
  53 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 52 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 189 3 17 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 189 (Polychromatic418967fa.accept_16_1_14_13_1_3834 49 78
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 189 3 16 26 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 189 3 15 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 44
  78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 189 3 14 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 41 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 78 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 189 3 13 26 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 37 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 189 3 12 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 34 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 189 3 11 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 189 3 10 26 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 189
  (Polychromatic418967fa.accept_14_1_8_7_1_1253 29 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 189 3 9 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 78 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 189
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 189 3 8 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 78 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 189 3 7 26 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 189 3 6 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 78 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 189 3 5 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 189 (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 78
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 189 3 4 26 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 189 3 3 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 78 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 189 3 2 26 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 189 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 78 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 189 3 1 26 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 78 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 78 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 189
  (allA_succ_of_accept 76 77 189 (accept_3_4 76 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 77 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 189 (accept_3_4 73 77 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 77 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 189
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 71 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 77 189 7 10 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 77 189 (Polychromatic418967fa.accept_13_4_12_7_1_2439 69 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 189 (accept_3_4 67 77 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 189 (Polychromatic418967fa.accept_18_12_5_9_1_6896
  66 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 189
  (Polychromatic418967fa.accept_19_8_1_18_1_5240 65 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 189 (accept_3_4 64 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 77
  189 7 9 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  77 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 77 189 (accept_3_4 61 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 77 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 189 (Polychromatic418967fa.accept_19_2_1_18_1_2660 59 77
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 189 (accept_3_4 58 77 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 189 (Polychromatic418967fa.accept_13_5_12_7_1_1080
  57 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 77 189 7 8 11 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 77 189 (accept_3_4 55
  77 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 189
  (Polychromatic418967fa.accept_24_6_5_21_1_10892 54 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 77 189 (Polychromatic418967fa.accept_15_8_2_9_1_3200 53 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 189 (accept_3_4 52 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 77 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 77 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 50
  77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 77 189 7 7 11 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 77 189
  (Polychromatic418967fa.accept_10_8_7_9_1_425 48 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 77 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 47 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 189 (accept_3_4 46 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 77 189 (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 77 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 77 189 (accept_3_4 43 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 77
  189 7 6 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  77 189 (Polychromatic418967fa.accept_15_11_2_9_1_1480 41 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 77 189 (accept_3_4 40 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 77 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 77 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 189 (accept_3_4 37 77 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 189
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 77 189 7 5 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 77 189 (accept_3_4 34 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 189 (Polychromatic418967fa.accept_18_15_5_9_1_5529 33 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 189 (accept_3_4 31 77 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 189 (Polychromatic418967fa.accept_13_4_12_7_1_2439 30 77 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 189
  (Polychromatic418967fa.accept_25_4_2_14_1_10891 29 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 77 189 7 4 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 77 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 189 (accept_3_4 25 77 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 189
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 77 189 (Polychromatic418967fa.accept_13_10_12_7_1_1079 23 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 189 (accept_3_4 22 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 77 189 7 3 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 77 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 189 (accept_3_4 19 77 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 77 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 189
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 189 (accept_3_4 16 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 77 189 7 2 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 77 189 (accept_3_4 13 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 77 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 189 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 77
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 189 (accept_3_4 10 77 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 189
  (Polychromatic418967fa.accept_22_9_11_13_1_10890 9 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 77 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 77 189 7 1 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 77 189 (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 77 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 189
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 189 (accept_3_4 4 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 77 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 189 (accept_3_4 1 77 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 189 (allA_succ_of_accept 75 76 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 75 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 189 (accept_3_5 74 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 189
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 72 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 189 (accept_3_5 71 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 189 (Polychromatic418967fa.accept_13_5_11_7_1_559 70 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 189 (Polychromatic418967fa.accept_13_4_11_7_1_558 69 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 189 (accept_3_5 68 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 66 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 189 (accept_3_5 65 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 189 (Polychromatic418967fa.accept_13_12_11_7_1_2491 64 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 189 (accept_3_5 62 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 189
  (Polychromatic418967fa.accept_25_10_1_14_1_10889 60 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 76 189 (accept_3_5 59 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 76 189 (Polychromatic418967fa.accept_16_10_12_13_1_4950 58 76 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 76 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 189 (accept_3_5 56 76 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 55
  76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 54 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 189 (accept_3_5 53 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500 52 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 189 (Polychromatic418967fa.accept_13_12_11_7_1_2491 51 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 189 (accept_3_5 50 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 189
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 189 (accept_3_5 47 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 189 (Polychromatic418967fa.accept_22_2_10_13_1_10888 46 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 189 (accept_3_5 44 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 189 (accept_3_5 41 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 189 (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 189 (Polychromatic418967fa.accept_20_19_16_9_1_9433 39 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 189 (accept_3_5 38 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 189
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 189 (accept_3_5 35 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 189 (accept_3_5 32 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 189 (accept_3_5 29 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 189 (Polychromatic418967fa.accept_17_11_8_2_1_3398 28 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 189 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 189 (accept_3_5 26 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 189
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 24 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 189 (accept_3_5 23 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 189 (Polychromatic418967fa.accept_13_9_11_7_1_1077 22 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 189 (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 189 (accept_3_5 20 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 189 (accept_3_5 17 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 189 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 189 (accept_3_5 14 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 189 (accept_3_5 11 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 189 (Polychromatic418967fa.accept_15_10_1_9_1_5356 10 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 189 (accept_3_5 8 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 189 (accept_3_5 5 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  189 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 76 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 189 (accept_3_5 2 76 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 189 (allA_succ_of_accept
  74 75 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 73 75 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 189 3 24 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 71 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 189 3 23 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 189 (Polychromatic418967fa.accept_13_3_10_7_1_1061
  68 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 67 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 189 3 22 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 65 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 64 75 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 189 3 21 25 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 61 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 189 3 20 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 59
  75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 189 3 19 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 56 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 75 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 189 3 18 25 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 53 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 189 (Polychromatic418967fa.accept_29_23_17_15_1_10887 52 75 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 189 3 17 25 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 189 3 16 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  47 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 75 189 3 15 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 75 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 44 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 75 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 189 3 14 25 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 75 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 75 189 3 13 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 189
  (Polychromatic418967fa.accept_11_4_9_2_1_259 37 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 189 3 12 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 75 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 189 3 11 25 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 189
  (Polychromatic418967fa.accept_17_15_7_2_1_2303 32 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 189 3 10 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 29
  75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 189
  (Polychromatic418967fa.accept_22_6_9_13_1_10886 28 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 75 189 3 9 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 75 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 75 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 189 3 8 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 189 3 7 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 189 (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 75 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 189 3 6 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 75 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 189 3 5 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 189 3 4 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 75 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 75 189 3 3 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 75 189 (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 75 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 189 3 2 25 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 75 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 189 3 1 25 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 1 75 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 189
  (allA_succ_of_accept 73 74 189 (accept_3_4 73 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  74 189 (Polychromatic418967fa.accept_15_12_14_9_1_778 72 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 189 (accept_3_4 70 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 74 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 69 74 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 68 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 74 189 (accept_3_4 67 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 189 (accept_3_4 64 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 189
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 62 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 74 189 (accept_3_4 61 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 74 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 74 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 189 (accept_3_4 58 74 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 189 (Polychromatic418967fa.accept_15_12_14_9_1_778
  57 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 189
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 56 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 189 (accept_3_4 55 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 189 (accept_3_4 52 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 189
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 50 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 189 (accept_3_4 49 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 189 (accept_3_4 46 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 74 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 189
  (Polychromatic418967fa.accept_16_12_10_13_1_1042 44 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 74 189 (accept_3_4 43 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 74 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 74 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 74 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 74 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 189 (accept_3_4 40 74 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 189 (accept_3_4 37 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 36 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 189 (accept_3_4 34 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 74 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 189
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 32 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 189 (accept_3_4 31 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 189 (accept_3_4 28 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 189
  (Polychromatic418967fa.accept_19_7_17_18_1_8155 26 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 189 (accept_3_4 25 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 189 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 189 (accept_3_4 22 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 189 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 74 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 189
  (Polychromatic418967fa.accept_15_5_14_9_1_274 20 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 189 (accept_3_4 19 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 189 (accept_3_4 16 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 189
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 74 189 (accept_3_4 13 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 74 189 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 74 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 189 (accept_3_4 10 74 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 189 (Polychromatic418967fa.accept_24_9_2_21_1_2251
  9 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 189 (accept_3_4 7 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 189 (accept_3_4 4 74 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 189 (Polychromatic418967fa.accept_13_2_9_7_1_164 2
  74 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 189 (accept_3_4 1 74 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 189 (allA_succ_of_accept
  72 73 189 (Polychromatic418967fa.accept_19_15_16_18_1_10885 72 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 189 (accept_3_5 71 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 73 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 189 (Polychromatic418967fa.accept_16_5_9_13_1_3845 69 73
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 189 (accept_3_5 68 73 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 189 (Polychromatic418967fa.accept_13_2_8_7_1_2424
  67 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 189
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 66 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 189 (accept_3_5 65 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 189 (accept_3_5 62 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 189 (Polychromatic418967fa.accept_13_9_8_7_1_1073 61 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 189 (accept_3_5 59 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 189 (Polychromatic418967fa.accept_18_3_1_9_1_1929 57 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 189 (accept_3_5 56 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135 55 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 189
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 189 (accept_3_5 53 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 189 (accept_3_5 50 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 189 (Polychromatic418967fa.accept_13_10_8_7_1_1074 49 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 189
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 48 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 189 (accept_3_5 47 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 189 (Polychromatic418967fa.accept_23_22_4_5_1_10884 45 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 189 (accept_3_5 44 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 189 (Polychromatic418967fa.accept_22_21_7_13_1_10883 43 73
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 189
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 189 (accept_3_5 41 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 189 (accept_3_5 38 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 189 (Polychromatic418967fa.accept_15_7_13_9_1_1466 37 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 189 (accept_3_5 35 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 189 (Polychromatic418967fa.accept_15_3_13_9_1_3196 33 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 189 (accept_3_5 32 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 73 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 189
  (Polychromatic418967fa.accept_20_10_13_9_1_6429 30 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 189 (accept_3_5 29 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 189 (accept_3_5 26 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 189 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 189
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 189 (accept_3_5 23 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 189 (Polychromatic418967fa.accept_16_5_9_13_1_3845 21 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 189 (accept_3_5 20 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 189 (Polychromatic418967fa.accept_15_4_13_9_1_3197 19 73
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 189
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 18 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 189 (accept_3_5 17 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 189 (accept_3_5 14 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 189 (Polychromatic418967fa.accept_19_13_16_18_1_10882 13 73 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 189 (accept_3_5 11 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 189 (accept_3_5 8 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 189 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 73 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 189
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 189 (accept_3_5 5 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 73 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 189 (accept_3_5 2 73 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 189 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 73 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 189 (allA_succ_of_accept 71
  72 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 71 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 70 72 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 189 3 23 24 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 189
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 68 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 67 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 189 3 22 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 189 (Polychromatic418967fa.accept_14_9_2_7_1_1242
  65 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 189
  (Polychromatic418967fa.accept_15_4_12_9_1_773 64 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 189 9 7 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 189 (Polychromatic418967fa.accept_20_2_12_9_1_6435 62 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 61 72 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 189 3 20 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 189
  (Polychromatic418967fa.accept_11_4_6_2_1_51 59 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 189 (Polychromatic418967fa.accept_22_14_6_13_1_10881 58 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 189 3 19 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 189 (Polychromatic418967fa.accept_23_10_3_5_1_10880
  56 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 189
  (Polychromatic418967fa.accept_15_10_12_9_1_776 55 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 189 9 6 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 189 (Polychromatic418967fa.accept_16_5_8_13_1_2764 53 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 189 (Polychromatic418967fa.accept_16_4_8_13_1_1059 52 72
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 189 3 17 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 189
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 50 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 189 (Polychromatic418967fa.accept_15_4_12_9_1_773 49 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 189 3 16 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 47
  72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 189
  (Polychromatic418967fa.accept_17_12_4_2_1_7116 46 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 189 9 5 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 189 (Polychromatic418967fa.accept_15_14_12_9_1_3216 44 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 189 (Polychromatic418967fa.accept_16_11_8_13_1_3844 43 72
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 189 3 14 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 189
  (Polychromatic418967fa.accept_10_1_2_9_1_152 41 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 189 (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 189 3 13 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 189 (Polychromatic418967fa.accept_22_16_6_13_1_6000
  38 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 189
  (Polychromatic418967fa.accept_10_7_2_9_1_775 37 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 189 9 4 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 189 (Polychromatic418967fa.accept_15_5_12_9_1_2253 35 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 189 (Polychromatic418967fa.accept_15_4_12_9_1_773 34 72 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 189 3 11 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 189
  (Polychromatic418967fa.accept_17_15_4_2_1_8419 32 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 31 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 189 3 10 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 189 (Polychromatic418967fa.accept_15_14_12_9_1_3216
  29 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 189
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 28 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 189 9 3 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 26 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 189 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 72
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 189 3 8 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 189
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 23 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 189 (Polychromatic418967fa.accept_19_3_15_18_1_2682 22 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 189 3 7 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 189 (Polychromatic418967fa.accept_15_5_12_9_1_2253 20 72 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 189
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 19 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 189 9 2 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 189 (Polychromatic418967fa.accept_19_16_15_18_1_5252 16 72
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 189 3 5 24 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 189
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 189 (Polychromatic418967fa.accept_25_13_22_14_1_10879 13 72 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 189 3 4 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 11
  72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 189
  (Polychromatic418967fa.accept_15_10_12_9_1_776 10 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 189 9 1 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 189 (Polychromatic418967fa.accept_23_8_3_5_1_10878 8 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 7 72 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 189 3 2 24 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 189
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 5 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 72 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 189 3 1 24 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 189 (Polychromatic418967fa.accept_19_2_15_18_1_1556 2 72 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 189
  (Polychromatic418967fa.accept_10_1_2_9_1_152 1 72 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 189
  (allA_succ_of_accept 70 71 189 (accept_3_4 70 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 69 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 189 (accept_3_4 67 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 65 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 189 (accept_3_4 64 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 189 (accept_3_4 61 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 189 (Polychromatic418967fa.accept_19_3_14_18_1_6685 60 71 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 189
  (Polychromatic418967fa.accept_36_23_35_9_1_10877 59 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 71 189 (accept_3_4 58 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 71 189 (Polychromatic418967fa.accept_16_9_7_13_1_4997 57 71 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 189 (accept_3_4 55 71 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 189
  (Polychromatic418967fa.accept_13_1_6_7_1_550 53 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 189 (accept_3_4 52 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 189 (accept_3_4 49 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 71 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 189
  (Polychromatic418967fa.accept_15_2_11_9_1_263 47 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 189 (accept_3_4 46 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 189 (accept_3_4 43 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 189 (accept_3_4 40 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 189 (accept_3_4 37 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 189 (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 71 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 189 (accept_3_4 34 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 189 (Polychromatic418967fa.accept_18_15_17_9_1_4200 33 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 189 (accept_3_4 31 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 189
  (Polychromatic418967fa.accept_19_10_14_18_1_10849 29 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 71 189 (accept_3_4 28 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 71 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 71 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 189 (accept_3_4 25 71 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 189
  (Polychromatic418967fa.accept_22_2_5_13_1_10876 24 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 71 189 (Polychromatic418967fa.accept_19_4_14_18_1_5234 23 71 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 189 (accept_3_4 22 71 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 71 189 (Polychromatic418967fa.accept_15_6_11_9_1_3215 21 71 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 189 (accept_3_4 19 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 189 (Polychromatic418967fa.accept_13_4_6_7_1_2471 17 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 189 (accept_3_4 16 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 71 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 189 (accept_3_4 13 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 189 (Polychromatic418967fa.accept_17_11_3_2_1_5867 11 71 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 189 (accept_3_4 10 71 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 71 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 189 (accept_3_4 7 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 71 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 189 (accept_3_4 4 71 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 71 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 189 (accept_3_4 1 71 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 189 (allA_succ_of_accept 69
  70 189 (Polychromatic418967fa.accept_18_15_16_9_1_4299 69 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 70 189 (accept_3_5 68 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 70 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 66 70 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 189 (accept_3_5 65 70 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 189 (Polychromatic418967fa.accept_11_9_4_2_1_600
  64 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 70 189 7 9 10 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 70 189 (accept_3_5 62
  70 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 70 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 61 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 70 189 (Polychromatic418967fa.accept_25_10_20_14_1_10874 60 70 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 189 (accept_3_5 59 70 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 189 (Polychromatic418967fa.accept_19_1_13_18_1_6700 58 70 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 189
  (Polychromatic418967fa.accept_15_12_10_9_1_798 57 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 70 189 7 8 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 70 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 70 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 70 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 189 (accept_3_5 53 70 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 189 (Polychromatic418967fa.accept_16_4_6_13_1_1874
  52 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 189 (accept_3_5 50 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 70
  189 7 7 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  70 189 (Polychromatic418967fa.accept_15_3_10_9_1_769 48 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 70 189 (accept_3_5 47 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 70 189 (Polychromatic418967fa.accept_15_1_10_9_1_1495 46 70 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 189 (Polychromatic418967fa.accept_20_5_10_9_1_9485 45 70
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 189 (accept_3_5 44 70 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 189 7 6 10 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 189 (accept_3_5 41
  70 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 189
  (Polychromatic418967fa.accept_24_16_22_21_1_5453 40 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 70 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 189 (accept_3_5 38 70 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 70 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 189
  (Polychromatic418967fa.accept_16_4_6_13_1_1874 36 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 70 189 7 5 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 70 189 (Polychromatic418967fa.accept_15_4_10_9_1_4298 34 70 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 189 (Polychromatic418967fa.accept_15_3_10_9_1_769 33 70 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 189 (accept_3_5 32 70 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 189 (accept_3_5 29 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70
  189 7 4 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  70 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 70 189 (accept_3_5 26 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 70 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 70 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 70
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 189 (accept_3_5 23 70 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 189
  (Polychromatic418967fa.accept_23_22_1_5_1_10875 22 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 70 189 7 3 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 70 189 (accept_3_5 20 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 189 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 70 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 189 (accept_3_5 17 70 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 189 (Polychromatic418967fa.accept_15_1_10_9_1_1495 16 70 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 70 189 7 2 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 70 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 70 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 189 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 70
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 189 (accept_3_5 11 70 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 189
  (Polychromatic418967fa.accept_25_10_20_14_1_10874 10 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 70 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 189 (accept_3_5 8 70 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 70 189 7 1 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 70 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 70 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 189 (accept_3_5 5 70 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 189 (Polychromatic418967fa.accept_15_4_10_9_1_4298 4 70 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 189 (accept_3_5 2 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 189
  (allA_succ_of_accept 68 69 189 (Polychromatic418967fa.accept_13_3_4_7_1_1711 68 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 67 69 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 189 3 22 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 189
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 65 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 189 (Polychromatic418967fa.accept_13_12_4_7_1_2520 64 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 189 3 21 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 189 (Polychromatic418967fa.accept_13_10_4_7_1_2465
  62 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 189
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 61 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 189 3 20 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 189 (Polychromatic418967fa.accept_18_5_15_9_1_1919 59 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 189 (Polychromatic418967fa.accept_13_6_4_7_1_2464 58 69 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 189 3 19 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 189
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 56 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 189 (Polychromatic418967fa.accept_13_3_4_7_1_1711 55 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 189 3 18 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 189 (Polychromatic418967fa.accept_18_17_15_9_1_5542
  53 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 189
  (Polychromatic418967fa.accept_18_16_15_9_1_6852 52 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 189 3 17 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 189 (Polychromatic418967fa.accept_13_11_4_7_1_2419 50 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 189 (Polychromatic418967fa.accept_13_10_4_7_1_2465 49 69
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 189 3 16 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 189
  (Polychromatic418967fa.accept_17_13_1_2_1_9714 47 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 189 (Polychromatic418967fa.accept_18_10_15_9_1_1054 46 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 189 3 15 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 189 (Polychromatic418967fa.accept_19_6_12_18_1_8141
  44 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 189
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 43 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 189 3 14 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 189 (Polychromatic418967fa.accept_16_9_5_13_1_4972 41 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 189 (Polychromatic418967fa.accept_16_8_5_13_1_1021 40 69
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 189 3 13 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 189
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 38 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 189 (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 189 3 12 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694
  35 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 189
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 189 3 11 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 189 (Polychromatic418967fa.accept_13_6_4_7_1_2464 32 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 189 (Polychromatic418967fa.accept_25_6_19_14_1_10873 31 69
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 189 3 10 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 189
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 189 (Polychromatic418967fa.accept_18_10_15_9_1_1054 28 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 189 3 9 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 189 (Polychromatic418967fa.accept_16_10_5_13_1_8591 26 69
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 189
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 189 3 8 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 22 69 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 189 3 7 23 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 189
  (Polychromatic418967fa.accept_14_6_13_7_1_2015 20 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 189 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 189 3 6 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 189 (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 69 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 189
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 189 3 5 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 189 (Polychromatic418967fa.accept_22_14_3_13_1_10872 14 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 189 (Polychromatic418967fa.accept_17_13_1_2_1_9714 13 69
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 189 3 4 23 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 189
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 189 (Polychromatic418967fa.accept_13_10_4_7_1_2465 10 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 189 3 3 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 189 (Polychromatic418967fa.accept_14_8_13_7_1_2798 8 69 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 189
  (Polychromatic418967fa.accept_19_7_12_18_1_10848 7 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 189 3 2 23 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 189 (Polychromatic418967fa.accept_18_5_15_9_1_1919 5 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 189 (Polychromatic418967fa.accept_18_4_15_9_1_6882 4 69 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 189 3 1 23 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 189
  (Polychromatic418967fa.accept_16_2_5_13_1_3842 2 69 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 69 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 189 (allA_succ_of_accept 67 68 189 (accept_3_4 67 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 68 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 68 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 68 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 189 (accept_3_4 64 68 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 189 (Polychromatic418967fa.accept_13_11_3_7_1_2513
  63 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 189
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 62 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 189 (accept_3_4 61 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455 60 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 189 (accept_3_4 58 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 68 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 189
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 56 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 189 (accept_3_4 55 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 189 (accept_3_4 52 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 68 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 189
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 50 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 189 (accept_3_4 49 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 189 (Polychromatic418967fa.accept_13_9_3_7_1_1065 48 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 189 (accept_3_4 46 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 189 (Polychromatic418967fa.accept_19_7_11_18_1_6680 45 68 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 44 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 189 (accept_3_4 43 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 189 (accept_3_4 40 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 189 (Polychromatic418967fa.accept_16_7_4_13_1_1057 39 68 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 189
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 38 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 189 (accept_3_4 37 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 189 (accept_3_4 34 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 68 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 189
  (Polychromatic418967fa.accept_15_2_8_9_1_4294 32 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 189 (accept_3_4 31 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 189 (accept_3_4 28 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 68 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 189
  (Polychromatic418967fa.accept_19_7_11_18_1_6680 26 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 189 (accept_3_4 25 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 189 (accept_3_4 22 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 68 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 189
  (Polychromatic418967fa.accept_19_1_11_18_1_10841 20 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 68 189 (accept_3_4 19 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 68 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 68 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 68 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 189 (accept_3_4 16 68 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 189
  (Polychromatic418967fa.accept_22_15_2_13_1_10871 15 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 68 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 68 189 (accept_3_4 13 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 68 189 (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 68 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 68 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 68 189 (accept_3_4 10 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  68 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 68 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455 8 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 68 189 (accept_3_4 7 68 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 68 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 68 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 68 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 68 189 (accept_3_4 4 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 68
  189 (Polychromatic418967fa.accept_15_3_8_9_1_795 3 68 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 68 189 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 68 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 189 (accept_3_4 1 68 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 189
  (allA_succ_of_accept 66 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 67 189 (accept_3_5 65 67 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 67 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  63 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 189 (accept_3_5 62
  67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 189
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 61 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 67 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 60 67 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 67 189 (accept_3_5 59 67 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 67 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414
  57 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 189 (accept_3_5 56
  67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 189
  (Polychromatic418967fa.accept_19_17_10_18_1_9563 55 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 67 189 (accept_3_5 53 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 67 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 67 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 67 189 (accept_3_5 50 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  67 189 (Polychromatic418967fa.accept_16_1_3_13_1_2785 49 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 67 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 67 189 (accept_3_5 47 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 189
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 67 189 (accept_3_5 44 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  67 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 189 (accept_3_5 41 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 67 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 67 189 (accept_3_5 38 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 189 (Polychromatic418967fa.accept_20_17_7_9_1_8001 37 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 189 (accept_3_5 35 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 189
  (Polychromatic418967fa.accept_16_1_3_13_1_2785 33 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 189 (accept_3_5 32 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 189 (Polychromatic418967fa.accept_13_5_2_7_1_2414 31 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 189 (accept_3_5 29 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 189 (accept_3_5 26 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 189 (Polychromatic418967fa.accept_14_10_11_7_1_1955 24 67 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 189 (accept_3_5 23 67 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 189
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 189 (accept_3_5 20 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 189 (Polychromatic418967fa.accept_23_19_21_5_1_10870 19 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 189 (accept_3_5 17 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 189 (accept_3_5 14 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 189 (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 189 (accept_3_5 11 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 189
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 189 (accept_3_5 8 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  189 (Polychromatic418967fa.accept_19_7_10_18_1_6695 7 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 67 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 189 (accept_3_5 5 67 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 189
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 189 (accept_3_5 2 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67
  189 (Polychromatic418967fa.accept_15_1_7_9_1_20 1 67 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 67 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 189
  (allA_succ_of_accept 65 66 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 65 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 64 66 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 189 3 21 22 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 62 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 66 189 (Polychromatic418967fa.accept_15_1_6_9_1_254 61 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 189 3 20 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 59
  66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 58 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 66 189 3 19 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 66 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 189 3 18 22 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 189
  (Polychromatic418967fa.accept_10_3_6_9_1_779 53 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 52 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 66 189 3 17 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 66 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 50
  66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 189
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 49 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 189 3 16 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 66 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 66 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 189 3 15 22 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 66 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 189 3 14 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 189 (Polychromatic418967fa.accept_15_11_6_9_1_3236
  41 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 66 189 3 13 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 66 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 66
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 189 3 12 22 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 189 3 11 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  32 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 189 3 10 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 66 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 189 3 9 22 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 66 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 189 3 8 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 66 189 3 7 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 66 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 189 3 6 22 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 189
  (Polychromatic418967fa.accept_14_3_10_7_1_3773 17 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 66 189 3 5 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 66 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 66 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 189
  (Polychromatic418967fa.accept_10_3_6_9_1_779 13 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 189 3 4 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 66 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 189 3 3 22 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 66 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 189 3 2 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 66 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 66 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 66 189 3 1 22 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 66 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 66 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 189 (Polychromatic418967fa.accept_15_1_6_9_1_254 1 66 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 189 (allA_succ_of_accept 64 65 189
  (accept_3_4 64 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 189
  (Polychromatic418967fa.accept_12_3_5_9_1_176 63 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 189 (accept_3_4 61 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 189 (Polychromatic418967fa.accept_15_14_5_9_1_2284
  59 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 189 (accept_3_4 58
  65 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 189
  (Polychromatic418967fa.accept_15_12_5_9_1_3234 57 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 189 (accept_3_4 55 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 189 (Polychromatic418967fa.accept_16_5_1_13_1_1053
  53 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 189 (accept_3_4 52
  65 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 51 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 189 (accept_3_4 49 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 65 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 48 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 189 (Polychromatic418967fa.accept_14_5_9_7_1_590
  47 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 189 (accept_3_4 46
  65 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 65 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 45 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 189 (accept_3_4 43 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 65 189 (Polychromatic418967fa.accept_15_12_5_9_1_3234 42 65 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 189 (accept_3_4 40 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 189 (accept_3_4 37 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 65 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 189
  (Polychromatic418967fa.accept_16_3_1_13_1_4968 35 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 189 (accept_3_4 34 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 189 (Polychromatic418967fa.accept_14_5_9_7_1_590 33 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 189 (accept_3_4 31 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 189 (Polychromatic418967fa.accept_14_2_9_7_1_5633 30 65 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 189
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 29 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 189 (accept_3_4 28 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 189 (accept_3_4 25 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 65 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 23 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 189 (accept_3_4 22 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 189 (accept_3_4 19 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 65 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 189
  (Polychromatic418967fa.accept_22_17_21_13_1_9291 17 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 65 189 (accept_3_4 16 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 65 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 189 (accept_3_4 13 65 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12
  65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 189 (accept_3_4 10 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 189 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 189 (accept_3_4 7 65 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 65 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 189
  (Polychromatic418967fa.accept_14_5_9_7_1_590 5 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 189 (accept_3_4 4 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 65 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 189 (accept_3_4 1 65 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 189
  (allA_succ_of_accept 63 64 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 189 (accept_3_5 62 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442
  60 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 189 (accept_3_5 59
  64 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 58 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 64 189 (Polychromatic418967fa.accept_13_5_12_7_1_1080 57 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 189 (accept_3_5 56 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 189 (Polychromatic418967fa.accept_12_6_4_9_1_544
  54 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 189 (accept_3_5 53
  64 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 189
  (Polychromatic418967fa.accept_17_1_13_2_1_7086 52 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 64 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 51 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 189 (accept_3_5 50 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  48 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 189 (accept_3_5 47
  64 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 189
  (Polychromatic418967fa.accept_19_8_7_18_1_1595 46 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 64 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 45 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 189 (accept_3_5 44 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 189 (Polychromatic418967fa.accept_12_6_4_9_1_544
  42 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 189 (accept_3_5 41
  64 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 189
  (Polychromatic418967fa.accept_11_7_9_2_1_260 40 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 64 189 (Polychromatic418967fa.accept_19_1_7_18_1_10869 39 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 189 (accept_3_5 38 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 189
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 189 (accept_3_5 35 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 34 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 189 (accept_3_5 32 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 189 (accept_3_5 29 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 189 (Polychromatic418967fa.accept_14_13_8_7_1_1224 27 64 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 189 (accept_3_5 26 64 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 189
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 189 (accept_3_5 23 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 189 (Polychromatic418967fa.accept_20_2_4_9_1_9524 22 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 64 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 189 (accept_3_5 20 64 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 189 (accept_3_5 17 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 189 (Polychromatic418967fa.accept_23_16_18_5_1_10868 16 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 189 (accept_3_5 14 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 189
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 12 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 189 (accept_3_5 11 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 189 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 189 (Polychromatic418967fa.accept_29_9_6_15_1_10867 9 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 189 (accept_3_5 8 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 189 (accept_3_5 5 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  189 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 64 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 189 (accept_3_5 2 64 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 189 (allA_succ_of_accept 62 63 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 189 3 20 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  59 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 189 3 19 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 63 189 7 8 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 63 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 189 9 6 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 63 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 189
  (Polychromatic418967fa.accept_20_12_3_9_1_10866 52 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 63 189 3 17 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 63 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63 189 7 7 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 63 189 3 16 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 63 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 63 189 9 5 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 44 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 63 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 189 21 2 3 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 189 (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 189 3 13 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 189 9 4 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 63 189 7 5 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 63 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 189 3 11 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 189 (Polychromatic418967fa.accept_20_12_3_9_1_10866
  32 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 189 3 10 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 189 7 4 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 63 189 9 3 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 63 189 3 8 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 63 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 189 21 1 3 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 189
  (Polychromatic418967fa.accept_15_5_3_9_1_283 20 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 189 9 2 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 63 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 189
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 189 3 5 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 63 189 7 2 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 63 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 189 3 4 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 189 9 1 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 189 (Polychromatic418967fa.accept_15_8_3_9_1_4220 8 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 189 7 1 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 63 189 3 2 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 63 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 189
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 63 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 189 3 1 21 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 63 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 189 (allA_succ_of_accept 61 62 189
  (accept_3_4 61 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 189
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 60 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 189 (accept_3_4 58 62 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 57 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701
  56 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 189 (accept_3_4 55
  62 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 189
  (Polychromatic418967fa.accept_12_6_2_9_1_537 54 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 62 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 189 (accept_3_4 52 62 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 189 (Polychromatic418967fa.accept_14_8_6_7_1_1934
  50 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 189 (accept_3_4 49
  62 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 189
  (Polychromatic418967fa.accept_19_10_5_18_1_10817 48 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 189 (accept_3_4 46 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 189 (Polychromatic418967fa.accept_22_1_18_13_1_10865 45 62 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 189
  (Polychromatic418967fa.accept_19_6_5_18_1_5228 44 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 189 (accept_3_4 43 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 189 (accept_3_4 40 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 189
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 38 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 189 (accept_3_4 37 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 189 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 189 (accept_3_4 34 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 189 (Polychromatic418967fa.accept_16_1_14_13_1_3834 33 62 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 189
  (Polychromatic418967fa.accept_19_13_5_18_1_8106 32 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 189 (accept_3_4 31 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 189 (accept_3_4 28 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 189
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 26 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 189 (accept_3_4 25 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 189 (Polychromatic418967fa.accept_18_6_8_9_1_1960 24 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 189 (accept_3_4 22 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 62 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 189
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 189 (accept_3_4 19 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 189 (accept_3_4 16 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 189
  (Polychromatic418967fa.accept_22_14_18_13_1_10864 14 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 62 189 (accept_3_4 13 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 62 189 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 62 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 189 (accept_3_4 10 62 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9
  62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 189
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 189 (accept_3_4 7 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 189 (accept_3_4 4 62 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 189 (Polychromatic418967fa.accept_19_2_5_18_1_10863
  2 62 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 189 (accept_3_4 1 62
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 189 (allA_succ_of_accept 60 61 189
  (Polychromatic418967fa.accept_13_8_9_7_1_530 60 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 189 (accept_3_5 59 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 189 (Polychromatic418967fa.accept_18_3_7_9_1_5486 57 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 189 (accept_3_5 56 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 55 61 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 189
  (Polychromatic418967fa.accept_13_2_9_7_1_164 54 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 189 (accept_3_5 53 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 189 (accept_3_5 50 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 189 (Polychromatic418967fa.accept_17_15_10_2_1_2309 49 61 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 189
  (Polychromatic418967fa.accept_10_8_1_9_1_413 48 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 189 (accept_3_5 47 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 189 (accept_3_5 44 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 61 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 189
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 189 (accept_3_5 41 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 189 (accept_3_5 38 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 61 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 189
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 189 (accept_3_5 35 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 189 (Polychromatic418967fa.accept_19_14_4_18_1_6665 33 61 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 189 (accept_3_5 32 61 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 189 (Polychromatic418967fa.accept_23_8_15_5_1_10862 31 61
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 189
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 189 (accept_3_5 29 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 189 (accept_3_5 26 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 61 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 189
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 189 (accept_3_5 23 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 189 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 189 (accept_3_5 20 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 189 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 61 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 189
  (Polychromatic418967fa.accept_10_8_1_9_1_413 18 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 189 (accept_3_5 17 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 189 (accept_3_5 14 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 189 (Polychromatic418967fa.accept_23_13_15_5_1_4120 13 61 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 189
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 189 (accept_3_5 11 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 189 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 189 (accept_3_5 8 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 189 (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 61 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 189
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 189 (accept_3_5 5 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 61 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 189 (accept_3_5 2 61 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 189 (Polychromatic418967fa.accept_24_1_13_21_1_9163 1 61 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 189 (allA_succ_of_accept 59 60 189 (Polychromatic418967fa.accept_14_3_4_7_1_175 59 60 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 189
  (Polychromatic418967fa.accept_16_10_12_13_1_4950 58 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 60 189 3 19 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 60 189 (Polychromatic418967fa.accept_16_8_12_13_1_3851 56 60 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 189
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 55 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 60 189 3 18 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 60 189 (Polychromatic418967fa.accept_13_1_8_7_1_1088 53 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 60 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 189 3 17 20 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 189
  (Polychromatic418967fa.accept_18_14_6_9_1_1950 50 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 60 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 189 3 16 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 189
  (Polychromatic418967fa.accept_16_15_12_13_1_1045 47 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 60 189 (Polychromatic418967fa.accept_22_2_16_13_1_10861 46 60 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 189 3 15 20 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 189
  (Polychromatic418967fa.accept_18_8_6_9_1_5576 44 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 189 (Polychromatic418967fa.accept_18_7_6_9_1_4205 43 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 189 3 14 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 41
  60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 189
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 40 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 60 189 3 13 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 189 (Polychromatic418967fa.accept_13_12_8_7_1_2526 38 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 189 (Polychromatic418967fa.accept_18_1_6_9_1_2001 37 60 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 189 3 12 20 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 189
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 35 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 189 (Polychromatic418967fa.accept_19_15_3_18_1_5241 34 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 189 3 11 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 189 (Polychromatic418967fa.accept_18_14_6_9_1_1950
  32 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 189
  (Polychromatic418967fa.accept_14_3_4_7_1_175 31 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 189 3 10 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135 29 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 189 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 60 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 189 3 9 20 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 189
  (Polychromatic418967fa.accept_16_10_12_13_1_4950 26 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 60 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 189 3 8 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 189 (Polychromatic418967fa.accept_13_10_8_7_1_1074
  23 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 189
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 22 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 60 189 3 7 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 60 189 (Polychromatic418967fa.accept_16_4_12_13_1_990 20 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 60 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 189 3 6 20 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 189 3 5 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 189 (Polychromatic418967fa.accept_13_1_8_7_1_1088 14 60 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 189
  (Polychromatic418967fa.accept_18_13_6_9_1_4280 13 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 189 3 4 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 189 (Polychromatic418967fa.accept_14_11_4_7_1_609 11 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 189 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 60
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 189 3 3 20 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 189 (Polychromatic418967fa.accept_17_7_9_2_1_629 7 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 189 3 2 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 189 (Polychromatic418967fa.accept_28_5_4_21_1_10860 5 60 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 189
  (Polychromatic418967fa.accept_16_4_12_13_1_990 4 60 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 60 189 3 1 20 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 60 189 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2 60 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 60 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  189)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 189 (allA_succ_of_accept 58 59 189
  (accept_3_4 58 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 189
  (Polychromatic418967fa.accept_15_12_14_9_1_778 57 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 189 (accept_3_4 55 59 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 189 (Polychromatic418967fa.accept_11_9_4_2_1_600
  53 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 189 (accept_3_4 52
  59 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 189
  (Polychromatic418967fa.accept_12_3_11_9_1_193 51 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 189 (accept_3_4 49 59 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 189 (Polychromatic418967fa.accept_18_12_5_9_1_6896 48 59 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 189
  (Polychromatic418967fa.accept_19_9_2_18_1_10859 47 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 189 (accept_3_4 46 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 189 (Polychromatic418967fa.accept_17_11_8_2_1_3398 45 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 189 (accept_3_4 43 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 189
  (Polychromatic418967fa.accept_19_3_2_18_1_9566 41 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 189 (accept_3_4 40 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 189 (accept_3_4 37 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 36 59 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 189
  (Polychromatic418967fa.accept_15_5_14_9_1_274 35 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 189 (accept_3_4 34 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 189 (Polychromatic418967fa.accept_17_16_8_2_1_5890 33 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 189 (accept_3_4 31 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 189
  (Polychromatic418967fa.accept_19_10_2_18_1_6674 29 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 189 (accept_3_4 28 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 189 (accept_3_4 25 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 189 (Polychromatic418967fa.accept_14_10_3_7_1_1975 24 59 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 189
  (Polychromatic418967fa.accept_15_8_14_9_1_4216 23 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 189 (accept_3_4 22 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 189 (accept_3_4 19 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 189
  (Polychromatic418967fa.accept_11_6_4_2_1_599 17 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 189 (accept_3_4 16 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 189 (accept_3_4 13 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 189 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 59 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 189
  (Polychromatic418967fa.accept_14_11_3_7_1_604 11 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 189 (accept_3_4 10 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 189 (accept_3_4 7 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 189
  (Polychromatic418967fa.accept_15_5_14_9_1_274 5 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 189 (accept_3_4 4 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 59 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 189 (accept_3_4 1 59 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 189
  (allA_succ_of_accept 57 58 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 57 58 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 189 (accept_3_5 56 58 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 189 (Polychromatic418967fa.accept_10_4_8_9_1_784
  54 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 189 (accept_3_5 53
  58 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 189
  (Polychromatic418967fa.accept_15_7_13_9_1_1466 52 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 189 (accept_3_5 50 58 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 189 (Polychromatic418967fa.accept_13_9_6_7_1_551
  48 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 189 (accept_3_5 47
  58 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 189
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 46 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 189 (accept_3_5 44 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 189 (accept_3_5 41 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 40 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 189 (accept_3_5 38 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 189
  (Polychromatic418967fa.accept_19_17_1_18_1_2693 36 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 189 (accept_3_5 35 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 189 (Polychromatic418967fa.accept_14_5_2_7_1_2804 33 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 189 (accept_3_5 32 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 189 (accept_3_5 29 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 189 (Polychromatic418967fa.accept_16_12_10_13_1_1042 28 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 189 (accept_3_5 26 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 58 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 24 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 189 (accept_3_5 23 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 22 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 189 (accept_3_5 20 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 189 (accept_3_5 17 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 189 (Polychromatic418967fa.accept_22_16_14_13_1_10858 16 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 189 (accept_3_5 14 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 189
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 189 (accept_3_5 11 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 189 (Polychromatic418967fa.accept_23_10_12_5_1_10857 10 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 189 (accept_3_5 8 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 189 (accept_3_5 5 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  189 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 58 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 189 (accept_3_5 2 58 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 189 (allA_succ_of_accept 56 57 189 (Polychromatic418967fa.accept_18_2_3_9_1_1996 56 57 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 189
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 55 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 57 189 3 18 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 57 189 (Polychromatic418967fa.accept_16_5_9_13_1_3845 53 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 57 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 189 3 17 19 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 189
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 50 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 189 (Polychromatic418967fa.accept_15_4_12_9_1_773 49 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 189 3 16 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 189 (Polychromatic418967fa.accept_17_13_6_2_1_5850
  47 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 189
  (Polychromatic418967fa.accept_17_12_6_2_1_2346 46 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 57 189 3 15 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 57 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 189 (Polychromatic418967fa.accept_18_7_3_9_1_1020 43 57 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 189 3 14 19 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 189
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 41 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 189 (Polychromatic418967fa.accept_15_10_12_9_1_776 40 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 189 3 13 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 38
  57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 189
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 57 189 3 12 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 57 189 (Polychromatic418967fa.accept_15_5_12_9_1_2253 35 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 189 (Polychromatic418967fa.accept_14_6_1_7_1_2775 34 57 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 189 3 11 19 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 189
  (Polychromatic418967fa.accept_10_2_7_9_1_783 32 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 189 (Polychromatic418967fa.accept_18_13_3_9_1_4233 31 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 189 3 10 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 189 (Polychromatic418967fa.accept_15_14_12_9_1_3216
  29 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 57 189 3 9 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 57 189 (Polychromatic418967fa.accept_18_8_3_9_1_4232 26 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 189 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 57
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 189 3 8 19 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 189
  (Polychromatic418967fa.accept_16_7_9_13_1_4948 23 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 22 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 189 3 7 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 57 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 189
  (Polychromatic418967fa.accept_15_4_12_9_1_773 19 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 57 189 3 6 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 57 189 (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 189 (Polychromatic418967fa.accept_23_16_11_5_1_10856 16 57
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 189 3 5 19 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 189
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 189 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 189 3 4 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 57 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 189
  (Polychromatic418967fa.accept_15_10_12_9_1_776 10 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 57 189 3 3 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 57 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 189 (Polychromatic418967fa.accept_16_7_9_13_1_4948 7 57 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 189 3 2 19 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 189
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 57 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 189 3 1 19 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 2 57 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 189
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 1 57 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 189 (allA_succ_of_accept 55 56
  189 (accept_3_4 55 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 56 189
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 56 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 189 (accept_3_4 52 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 56 189 (Polychromatic418967fa.accept_13_12_4_7_1_2520 51 56 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 189
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 50 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 56 189 7 7 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 56 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 56 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 189 (accept_3_4 46 56 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235
  45 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 189
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 44 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 189 (accept_3_4 43 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  189 7 6 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 56 189 (accept_3_4 40 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 56 189 (Polychromatic418967fa.accept_18_3_2_9_1_1013 39 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 189 (Polychromatic418967fa.accept_13_12_4_7_1_2520 38 56
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 189 (accept_3_4 37 56 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063
  36 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 56 189 7 5 8 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 56 189 (accept_3_4 34
  56 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 189
  (Polychromatic418967fa.accept_10_3_6_9_1_779 33 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 56 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 189 (accept_3_4 31 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 56 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 56 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 56 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29
  56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 189 7 4 8 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 189
  (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 56 189 (Polychromatic418967fa.accept_22_4_12_13_1_10855 26 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 189 (accept_3_4 25 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 56 189 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 56 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 56 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 56 189 (accept_3_4 22 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 56
  189 7 3 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  56 189 (Polychromatic418967fa.accept_15_5_11_9_1_4276 20 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 56 189 (accept_3_4 19 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 56 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 189 (accept_3_4 16 56 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235
  15 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 189 7 2 8 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 189 (accept_3_4 13
  56 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 189
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 56 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 189 (accept_3_4 10 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 56 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 56 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 189 (Polychromatic418967fa.accept_25_8_6_14_1_10854
  8 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 56 189 7 1 8 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 56 189
  (Polychromatic418967fa.accept_12_6_8_9_1_553 6 56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 189 (accept_3_4 4 56 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 56 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 189 (Polychromatic418967fa.accept_15_2_11_9_1_263 2
  56 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 189 (accept_3_4 1 56 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 189))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 189 (allA_succ_of_accept 54 55 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 189 (accept_3_5 53 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 51 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 189 (accept_3_5 50 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 189 (Polychromatic418967fa.accept_13_9_3_7_1_1065 48 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 189 (accept_3_5 47 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 189
  (Polychromatic418967fa.accept_19_7_17_18_1_8155 45 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 189 (accept_3_5 44 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 189 (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 189 (accept_3_5 41 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 189 (accept_3_5 38 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 189 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 189 (accept_3_5 35 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 189
  (Polychromatic418967fa.accept_15_3_10_9_1_769 33 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 189 (accept_3_5 32 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 189 (accept_3_5 29 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 189 (accept_3_5 26 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 189 (Polychromatic418967fa.accept_16_9_7_13_1_4997 25 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 189 (accept_3_5 23 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 21 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 189 (accept_3_5 20 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 189 (Polychromatic418967fa.accept_15_4_10_9_1_4298 19 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 189 (accept_3_5 17 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 189 (accept_3_5 14 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 189 (Polychromatic418967fa.accept_19_13_17_18_1_6638 13 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 189 (Polychromatic418967fa.accept_15_12_10_9_1_798 12 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 189 (accept_3_5 11 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 189
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 189 (accept_3_5 8 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  189 (Polychromatic418967fa.accept_19_7_17_18_1_8155 7 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 55 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 189 (accept_3_5 5 55 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 189 (accept_3_5 2 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  189 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 55 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 55 189))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 189 (allA_succ_of_accept 53 54
  189 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 52 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 189 3 17 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 50
  54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 189
  (Polychromatic418967fa.accept_22_5_10_13_1_10853 49 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 54 189 3 16 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 54 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 54 189 9 5 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 54 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 189 3 14 18 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 189
  (Polychromatic418967fa.accept_16_9_6_13_1_3831 41 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 189 3 13 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  38 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 189
  (Polychromatic418967fa.accept_14_9_12_7_1_597 37 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 189 9 4 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 54 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 189 3 11 18 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 189 3 10 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 189 (Polychromatic418967fa.accept_24_5_6_21_1_10852
  29 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 54 189 27 1 2 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 54 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 25 54 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 189 3 8 18 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 189 3 7 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 54 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 189 9 2 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 189 (Polychromatic418967fa.accept_19_17_16_18_1_2684 17 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 54 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 189 3 5 18 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 189 3 4 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 54 189 9 1 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 54 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 189 3 2 18 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 189
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 54 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 189 3 1 18 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 54 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 1 54 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 189)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 189 (allA_succ_of_accept 52 53
  189 (accept_3_4 52 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 189
  (Polychromatic418967fa.accept_11_7_9_2_1_260 51 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 189 (accept_3_4 49 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 53 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 189 (Polychromatic418967fa.accept_13_8_1_7_1_2505
  47 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 189 (accept_3_4 46
  53 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 189
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 189 (accept_3_4 43 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706 42 53 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 189 (Polychromatic418967fa.accept_16_9_5_13_1_4972
  41 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 189 (accept_3_4 40
  53 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 189
  (Polychromatic418967fa.accept_12_3_5_9_1_176 39 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 189 (accept_3_4 37 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 53 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 189
  (Polychromatic418967fa.accept_19_16_15_18_1_5252 35 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 53 189 (accept_3_4 34 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 53 189 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 189 (accept_3_4 31 53 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 189
  (Polychromatic418967fa.accept_18_12_17_9_1_5513 30 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 53 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 189 (accept_3_4 28 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 53 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 53 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 26
  53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 189 (accept_3_4 25 53
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 189
  (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 53 189 (Polychromatic418967fa.accept_19_4_15_18_1_10821 23 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 189 (accept_3_4 22 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 53 189 (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 53 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 189 (accept_3_4 19 53
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 189
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 53 189 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 189 (accept_3_4 16 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 53 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 53 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 14
  53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 189 (accept_3_4 13 53
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 189
  (Polychromatic418967fa.accept_18_12_17_9_1_5513 12 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 53 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 11 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 189 (accept_3_4 10 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 53 189 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 53 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 189 (accept_3_4 7 53 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6
  53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 189
  (Polychromatic418967fa.accept_25_5_3_14_1_10851 5 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 189 (accept_3_4 4 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 53 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 189 (accept_3_4 1 53 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 189))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 189
  (allA_succ_of_accept 51 52 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 52 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 189 (accept_3_5 50 52 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 189
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 48 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 189 (accept_3_5 47 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 189 (Polychromatic418967fa.accept_14_4_10_7_1_1946 46 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 189 (Polychromatic418967fa.accept_14_3_10_7_1_3773 45 52 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 189 (accept_3_5 44 52 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 189 (accept_3_5 41 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 189 (Polychromatic418967fa.accept_16_8_4_13_1_1014 40 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 189 (Polychromatic418967fa.accept_14_11_10_7_1_1948 39 52 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 189 (accept_3_5 38 52 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 189
  (Polychromatic418967fa.accept_28_8_24_21_1_10850 36 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 52 189 (accept_3_5 35 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 52 189 (Polychromatic418967fa.accept_19_15_14_18_1_6696 34 52 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 52 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 189 (accept_3_5 32 52 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 189 (accept_3_5 29 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 189 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 52 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 189 (accept_3_5 26 52 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 189
  (Polychromatic418967fa.accept_16_8_4_13_1_1014 24 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 189 (accept_3_5 23 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 189 (Polychromatic418967fa.accept_16_6_4_13_1_3841 22 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 52 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 189 (accept_3_5 20 52 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 189 (accept_3_5 17 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 189 (Polychromatic418967fa.accept_18_15_16_9_1_4299 15 52 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 189 (accept_3_5 14 52 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 189
  (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 189 (accept_3_5 11 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 189 (Polychromatic418967fa.accept_19_10_14_18_1_10849 10 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 52 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 189 (accept_3_5 8 52 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 189 (accept_3_5 5 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  189 (Polychromatic418967fa.accept_14_4_10_7_1_1946 4 52 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 189 (Polychromatic418967fa.accept_14_3_10_7_1_3773 3 52 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 189 (accept_3_5 2 52 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  189)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 189 (allA_succ_of_accept 50 51 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 189 3 16 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  47 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 189 3 15 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 189 (Polychromatic418967fa.accept_13_5_12_7_1_1080 44 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 51 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 189 3 14 17 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 189 (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 189 3 13 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 189 3 12 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 189 3 11 17 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 189
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 189 3 10 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 29
  51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 189
  (Polychromatic418967fa.accept_10_8_1_9_1_413 28 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 189 3 9 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 25 51 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 189 3 8 17 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 189 3 7 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 51 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 189 3 6 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 189 (Polychromatic418967fa.accept_14_2_9_7_1_5633 16 51 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 189 3 5 17 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 189 3 4 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 51 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 189 3 3 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 51 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 189 3 2 17 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 189 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 51 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 189 3 1 17 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 51 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 189))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 189 (allA_succ_of_accept 49 50 189
  (accept_3_4 49 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 189
  (Polychromatic418967fa.accept_11_4_6_2_1_51 48 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 189 (accept_3_4 46 50 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 189 (Polychromatic418967fa.accept_19_7_12_18_1_10848 45 50 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 189
  (Polychromatic418967fa.accept_13_5_11_7_1_559 44 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 189 (accept_3_4 43 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 189 (accept_3_4 40 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 189
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 38 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 189 (accept_3_4 37 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 189 (Polychromatic418967fa.accept_19_17_12_18_1_5248 36 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 189 (accept_3_4 34 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 50 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 189
  (Polychromatic418967fa.accept_19_13_12_18_1_2677 32 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 50 189 (accept_3_4 31 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 50 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 50 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 50 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 189 (accept_3_4 28 50 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 189
  (Polychromatic418967fa.accept_11_4_6_2_1_51 26 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 189 (accept_3_4 25 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 189 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 189 (accept_3_4 22 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 189 (Polychromatic418967fa.accept_16_5_2_13_1_1007 21 50 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 189
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 189 (accept_3_4 19 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 189 (accept_3_4 16 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 189
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 189 (accept_3_4 13 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 189 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 189 (accept_3_4 10 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 189 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 50 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 189
  (Polychromatic418967fa.accept_17_8_16_2_1_10847 8 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 189 (accept_3_4 7 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 50 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 189 (accept_3_4 4 50 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 189 (Polychromatic418967fa.accept_26_2_24_7_1_9056
  2 50 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 189 (accept_3_4 1 50
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 189))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 49 189 (allA_succ_of_accept 48 49 189 (Polychromatic418967fa.accept_19_10_11_18_1_10846 48 49 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 189 (accept_3_5 47 49 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 189
  (Polychromatic418967fa.accept_19_7_11_18_1_6680 45 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 189 (accept_3_5 44 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 43 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 49 189 7 6 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 49 189 (accept_3_5 41 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 49 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 49 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 189 (accept_3_5 38 49 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 189 (Polychromatic418967fa.accept_16_5_1_13_1_1053
  37 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 49 189 7 5 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 49 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 49 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 189 (Polychromatic418967fa.accept_22_11_5_13_1_10845 33 49
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 189 (accept_3_5 32 49 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 189
  (Polychromatic418967fa.accept_19_12_11_18_1_10844 31 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 49 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 189 (accept_3_5 29 49 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49 189 7 4 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 49 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 189 (accept_3_5 26 49 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 189 (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 49
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 189
  (Polychromatic418967fa.accept_17_7_15_2_1_10843 24 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 189 (accept_3_5 23 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 49 189 7 3 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 49 189 (accept_3_5 20 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 49 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 49 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 189 (Polychromatic418967fa.accept_22_18_5_13_1_10842 18 49
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 189 (accept_3_5 17 49 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 49 189 7 2 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 49 189 (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 49 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 189 (accept_3_5 11 49 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10
  49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 189
  (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 189 (accept_3_5 8 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 189
  7 1 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 49 189
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 6 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 189 (accept_3_5 5 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 189 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 49 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 189 (accept_3_5 2 49 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 189 (Polychromatic418967fa.accept_19_1_11_18_1_10841 1 49 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 189)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 189 (allA_succ_of_accept 47 48 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 47 48 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 189
  (Polychromatic418967fa.accept_18_10_12_9_1_2012 46 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 48 189 3 15 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 48 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 44 48 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 48 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 189 3 14 16 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 189
  (Polychromatic418967fa.accept_10_1_8_9_1_787 41 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 189 (Polychromatic418967fa.accept_15_10_3_9_1_3285 40 48 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 48 189 3 13 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 48 189 (Polychromatic418967fa.accept_15_8_3_9_1_4220
  38 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 189
  (Polychromatic418967fa.accept_10_7_8_9_1_785 37 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 189 3 12 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 189 (Polychromatic418967fa.accept_15_5_3_9_1_283 35 48 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 34 48 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 189 3 11 16 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 189
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 32 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 48 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 31 48 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 189 3 10 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 189 (Polychromatic418967fa.accept_13_3_9_7_1_1730
  29 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 189
  (Polychromatic418967fa.accept_11_6_4_2_1_599 28 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 48 189 3 9 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 48 189 (Polychromatic418967fa.accept_19_7_10_18_1_6695 26 48 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 189 (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 48
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 189 3 8 16 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 189
  (Polychromatic418967fa.accept_15_8_3_9_1_4220 23 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 189 (Polychromatic418967fa.accept_14_8_6_7_1_1934 22 48 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 189 3 7 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 48 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 189
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 189 3 6 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 48 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 189 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 48 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 189 3 5 16 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 189 (Polychromatic418967fa.accept_14_13_6_7_1_2013 13 48 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 189 3 4 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 11 48 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 189
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 10 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 48 189 3 3 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 48 189 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 48 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 7 48 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 189 3 2 16 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 189
  (Polychromatic418967fa.accept_15_5_3_9_1_283 5 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 48 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 189 3 1 16 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 189 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 48 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 189
  (Polychromatic418967fa.accept_10_1_8_9_1_787 1 48 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 189)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 189 (allA_succ_of_accept 46 47 189
  (accept_3_4 46 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 189
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 189 (accept_3_4 43 47 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 189 (Polychromatic418967fa.accept_13_2_8_7_1_2424
  41 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 189 (accept_3_4 40
  47 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 189
  (Polychromatic418967fa.accept_12_3_11_9_1_193 39 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 189 (accept_3_4 37 47 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 189 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 47 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 189
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 35 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 189 (accept_3_4 34 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 189 (Polychromatic418967fa.accept_18_15_11_9_1_4256 33 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 189 (accept_3_4 31 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 189
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 29 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 189 (accept_3_4 28 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 189 (accept_3_4 25 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 189 (Polychromatic418967fa.accept_17_7_13_2_1_10840 24 47 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 189
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 189 (accept_3_4 22 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 189 (Polychromatic418967fa.accept_19_2_9_18_1_6651 21 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 189 (accept_3_4 19 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 189
  (Polychromatic418967fa.accept_20_17_7_9_1_8001 17 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 189 (accept_3_4 16 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 189 (accept_3_4 13 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 47 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 189
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 189 (accept_3_4 10 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 189 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 189 (accept_3_4 7 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 189
  (Polychromatic418967fa.accept_19_5_9_18_1_10839 5 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 189 (accept_3_4 4 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 47 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 189 (accept_3_4 1 47 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 189))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 189
  (allA_succ_of_accept 45 46 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 45 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 189 (accept_3_5 44 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 46 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  42 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 189 (accept_3_5 41
  46 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 189
  (Polychromatic418967fa.accept_15_10_1_9_1_5356 40 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 189 (accept_3_5 38 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 189 (Polychromatic418967fa.accept_15_6_1_9_1_1476
  36 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 189 (accept_3_5 35
  46 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 189
  (Polychromatic418967fa.accept_20_14_6_9_1_9460 34 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 46 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 189 (accept_3_5 32 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 46 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  30 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 189 (accept_3_5 29
  46 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 189
  (Polychromatic418967fa.accept_19_9_8_18_1_1571 28 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 189 (accept_3_5 26 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 189 (Polychromatic418967fa.accept_14_10_4_7_1_1214
  24 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 189 (accept_3_5 23
  46 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 189
  (Polychromatic418967fa.accept_15_7_1_9_1_1500 22 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 189 (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 189 (accept_3_5 20 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  18 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 189 (accept_3_5 17
  46 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 189
  (Polychromatic418967fa.accept_19_16_8_18_1_8139 16 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 46 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 189 (accept_3_5 14 46 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 46 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 189
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 46 189 (accept_3_5 11 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  46 189 (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 46 189 (Polychromatic418967fa.accept_19_9_8_18_1_1571 9 46 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 189 (accept_3_5 8 46 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 46 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 46 189 (accept_3_5 5 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46
  189 (Polychromatic418967fa.accept_17_4_12_2_1_2349 4 46 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 46 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 189 (accept_3_5 2 46 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 189))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 45 189 (allA_succ_of_accept 44 45 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 44 45 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 189
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 45 189 3 14 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 45 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 45 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 40 45 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 45 189 3 13 15 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 189
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 38 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 189 (Polychromatic418967fa.accept_17_3_11_2_1_8435 37 45 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 189 9 4 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 35 45 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 189
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 34 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 45 189 3 11 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 45 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 45 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 31 45 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 189 3 10 15 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 189
  (Polychromatic418967fa.accept_19_10_7_18_1_10838 29 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 189 (Polychromatic418967fa.accept_29_28_16_15_1_10837 28 45 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 189 9 3 5 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 189
  (Polychromatic418967fa.accept_10_6_5_9_1_1233 26 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 45 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 189 3 8 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 189 (Polychromatic418967fa.accept_30_23_15_9_1_10836 23 45
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 189
  (Polychromatic418967fa.accept_13_9_6_7_1_551 22 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 189 3 7 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 189 (Polychromatic418967fa.accept_17_3_11_2_1_8435 20 45 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 189 (Polychromatic418967fa.accept_25_19_20_14_1_10835 19 45
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 189 9 2 5 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 189
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 17 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 45 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 189 3 5 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 14 45 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 189
  (Polychromatic418967fa.accept_26_13_19_7_1_10834 13 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 45 189 3 4 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 45 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 45 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624
  10 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 189 9 1 5 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 189
  (Polychromatic418967fa.accept_17_8_11_2_1_3415 8 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 189 (Polychromatic418967fa.accept_20_7_5_9_1_10833 7 45 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 189 3 2 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 189 (Polychromatic418967fa.accept_28_5_17_21_1_10832 5 45 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 189
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 45 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 189 3 1 15 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 189 (Polychromatic418967fa.accept_23_2_22_5_1_10831 2 45 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 45 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  189))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 189 (allA_succ_of_accept 43 44 189 (accept_3_4 43 44
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 189
  (Polychromatic418967fa.accept_12_6_8_9_1_553 42 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 189 (accept_3_4 40 44 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 189 (Polychromatic418967fa.accept_18_3_8_9_1_1956 39 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229
  38 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 189 (accept_3_4 37
  44 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 189
  (Polychromatic418967fa.accept_15_6_14_9_1_1471 36 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 189 (accept_3_4 34 44 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 189
  (Polychromatic418967fa.accept_17_15_10_2_1_2309 32 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 189 (accept_3_4 31 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 189 (accept_3_4 28 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 189 (Polychromatic418967fa.accept_15_12_14_9_1_778 27 44 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 189
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 189 (accept_3_4 25 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 189 (accept_3_4 22 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 189 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 44 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 189
  (Polychromatic418967fa.accept_15_5_14_9_1_274 20 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 189 (accept_3_4 19 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 189 (accept_3_4 16 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 189 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 44 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 189
  (Polychromatic418967fa.accept_20_14_4_9_1_2249 14 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 189 (accept_3_4 13 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 189 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 189 (accept_3_4 10 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 44 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 189 (accept_3_4 7 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 189 (accept_3_4 4 44 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 44 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 189 (Polychromatic418967fa.accept_13_2_5_7_1_1695 2
  44 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 189 (accept_3_4 1 44 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 189)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  189 (allA_succ_of_accept 42 43 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 189 (accept_3_5 41 43 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  39 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 189 (accept_3_5 38
  43 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 189
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 43 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 43 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 189 (accept_3_5 35 43 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 43 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 189 (Polychromatic418967fa.accept_15_3_13_9_1_3196
  33 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 189 (accept_3_5 32
  43 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 189
  (Polychromatic418967fa.accept_22_9_21_13_1_10830 31 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 189 (accept_3_5 29 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 189 (accept_3_5 26 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 189 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 189 (accept_3_5 23 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 189
  (Polychromatic418967fa.accept_17_4_9_2_1_9721 21 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 189 (accept_3_5 20 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 189 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 189 (accept_3_5 17 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 189 (accept_3_5 14 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 189 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 189 (accept_3_5 11 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 189
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 189 (accept_3_5 8 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  189 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 43 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 189 (accept_3_5 5 43 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 189
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 189 (accept_3_5 2 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43
  189 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 43 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 43 189))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 189 (allA_succ_of_accept 41 42 189
  (Polychromatic418967fa.accept_10_1_2_9_1_152 41 42 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 42 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 189 3 13 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 38
  42 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 189
  (Polychromatic418967fa.accept_10_7_2_9_1_775 37 42 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 189 3 12 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 42 189 7 5 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 42 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 42 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 189 3 11 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  32 42 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 189 3 10 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 42 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 189 7 4 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 189 3 9 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 26 42 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 189
  (Polychromatic418967fa.accept_15_10_12_9_1_776 25 42 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 189 3 8 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 42 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 189 21 1 2 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 42 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 189 3 6 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 189 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 42 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 189
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 42 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 189 3 5 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 42 189 7 2 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 189 (Polychromatic418967fa.accept_18_13_6_9_1_4280 13 42 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 189 3 4 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 189
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 42 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 42 189 3 3 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 42 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 42 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 189 7 1 6 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 189 3 2 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 189 (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 42 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 189
  (Polychromatic418967fa.accept_11_4_9_2_1_259 4 42 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 42 189 3 1 14 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 42 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 42 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 1 42 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  189)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 189 (allA_succ_of_accept 40 41 189 (accept_3_4 40 41 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 189 (Polychromatic418967fa.accept_12_3_5_9_1_176
  39 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 189 (accept_3_4 37 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 41 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 189 (accept_3_4 34 41 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 189 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 41 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 189 (accept_3_4 31 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 189 (Polychromatic418967fa.accept_17_13_7_2_1_4562 30 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 189 (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 41 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 189 (accept_3_4 28 41 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 41 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 189 (accept_3_4 25 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 189 (Polychromatic418967fa.accept_22_2_19_13_1_10829 24 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 189 (Polychromatic418967fa.accept_16_7_9_13_1_4948 23 41 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 189 (accept_3_4 22 41 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 41 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 189 (accept_3_4 19 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 189 (Polychromatic418967fa.accept_15_2_11_9_1_263 17 41 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 189 (accept_3_4 16 41 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 41 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 189 (accept_3_4 13 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 189 (Polychromatic418967fa.accept_19_11_3_18_1_10828 11 41 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 189 (accept_3_4 10 41 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 189 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 41 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 189 (accept_3_4 7 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  189 (Polychromatic418967fa.accept_14_6_13_7_1_2015 6 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 41 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 41 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 189 (accept_3_4 4 41 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 41 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 41 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 41 189 (accept_3_4 1 41 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41
  189))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 189 (allA_succ_of_accept 39 40 189
  (Polychromatic418967fa.accept_19_1_2_18_1_10827 39 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 189 (accept_3_5 38 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 189 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 40 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 189 (accept_3_5 35 40 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 189 (Polychromatic418967fa.accept_13_8_1_7_1_2505 34 40 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 189
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 33 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 189 (accept_3_5 32 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 40 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 189 (accept_3_5 29 40 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 189 (Polychromatic418967fa.accept_16_12_8_13_1_6073 28 40 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 189
  (Polychromatic418967fa.accept_15_12_10_9_1_798 27 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 189 (accept_3_5 26 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 189 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 40 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 189 (accept_3_5 23 40 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 189 (Polychromatic418967fa.accept_19_3_2_18_1_9566 22 40
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 189
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 189 (accept_3_5 20 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 40 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 189 (accept_3_5 17 40 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 40 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 189
  (Polychromatic418967fa.accept_18_15_4_9_1_4204 15 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 189 (accept_3_5 14 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 189 (Polychromatic418967fa.accept_15_12_10_9_1_798 12 40 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 189 (accept_3_5 11 40 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 189 (Polychromatic418967fa.accept_19_10_2_18_1_6674 10 40
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 189
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 189 (accept_3_5 8 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 40 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 189 (accept_3_5 5 40 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 189 (Polychromatic418967fa.accept_15_4_10_9_1_4298 4 40 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3
  40 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 189 (accept_3_5 2 40 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  189)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 189 (allA_succ_of_accept 38 39 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 39 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 189 3 12 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 39 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 189 3 11 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 189 (Polychromatic418967fa.accept_14_4_11_7_1_1234 32 39 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 39 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 189 3 10 13 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 39 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 189 (Polychromatic418967fa.accept_20_8_19_9_1_6417 28 39 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 189 3 9 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 39 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 189 3 8 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 39 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 189 3 7 13 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 189
  (Polychromatic418967fa.accept_16_4_7_13_1_2795 20 39 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 39 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 189 3 6 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 39 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 189
  (Polychromatic418967fa.accept_17_16_5_2_1_9724 16 39 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 189 3 5 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 39 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 189 3 4 13 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 189
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 39 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 189 3 3 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 189 (Polychromatic418967fa.accept_18_8_3_9_1_4232 8 39 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 39 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 189 3 2 13 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 39 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 39 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 189 3 1 13 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 39 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 189))))))))))))))))))))))))))))))))))))))) (allB_succ 38 189
  (allA_succ_of_accept 37 38 189 (accept_3_4 37 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 189 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 189 (accept_3_4 34 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 189 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 38 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 189
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 32 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 189 (accept_3_4 31 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 189 (accept_3_4 28 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 189
  (Polychromatic418967fa.accept_17_9_4_2_1_2298 26 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 189 (accept_3_4 25 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 189 (accept_3_4 22 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 21 38 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 189
  (Polychromatic418967fa.accept_16_4_6_13_1_1874 20 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 189 (accept_3_4 19 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 189 (accept_3_4 16 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 189 (accept_3_4 13 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 189 (Polychromatic418967fa.accept_17_12_4_2_1_7116 12 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 189 (accept_3_4 10 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 189 (Polychromatic418967fa.accept_16_9_6_13_1_3831 9 38 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 189
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 189 (accept_3_4 7 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  189 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 189 (accept_3_4 4 38 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 189 (Polychromatic418967fa.accept_15_2_8_9_1_4294 2
  38 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 189 (accept_3_4 1 38 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 189)))))))))))))))))))))))))))))))))))))) (allB_succ 37 189
  (allA_succ_of_accept 36 37 189 (Polychromatic418967fa.accept_22_14_15_13_1_10826 36 37 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 189 (accept_3_5 35 37 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 37 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 189
  (Polychromatic418967fa.accept_14_5_9_7_1_590 33 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 37 189 (accept_3_5 32 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  37 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 189 (Polychromatic418967fa.accept_13_4_11_7_1_558 30 37 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 189 (accept_3_5 29 37 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 189 (accept_3_5 26 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 189 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 189 (Polychromatic418967fa.accept_16_8_5_13_1_1021 24 37 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 189 (accept_3_5 23 37 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 189
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 21 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 189 (accept_3_5 20 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 189 (Polychromatic418967fa.accept_14_5_9_7_1_590 19 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 189 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 37 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 189 (accept_3_5 17 37 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 189 (accept_3_5 14 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 189 (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 189 (Polychromatic418967fa.accept_10_2_7_9_1_783 12 37 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 189 (accept_3_5 11 37 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 189 (accept_3_5 8 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  189 (Polychromatic418967fa.accept_20_7_17_9_1_10825 7 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 189 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 37 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 189 (accept_3_5 5 37 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 189 (accept_3_5 2 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  189 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 37 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 37 189))))))))))))))))))))))))))))))))))))) (allB_succ 36 189 (allA_succ_of_accept 35 36 189
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 36 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 189 (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 36 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 189 3 11 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 189
  (Polychromatic418967fa.accept_19_13_17_18_1_6638 32 36 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 36 189 (Polychromatic418967fa.accept_15_1_6_9_1_254 31 36 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 189 3 10 12 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 189
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 29 36 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 189 (Polychromatic418967fa.accept_16_12_4_13_1_3827 28 36 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 189 9 3 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 189 (Polychromatic418967fa.accept_15_11_6_9_1_3236 26 36 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 189
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 36 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 189 3 8 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 36 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 189 (Polychromatic418967fa.accept_16_6_4_13_1_3841 22 36
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 189 3 7 12 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 189
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 36 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 189 (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 36 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 189 9 2 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 36 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 189
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 36 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 36 189 3 5 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 36 189 (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 36 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 36 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 189 3 4 12 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 189
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 36 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 189 (Polychromatic418967fa.accept_19_10_17_18_1_9555 10 36 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 189 9 1 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 189 (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 36 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 189
  (Polychromatic418967fa.accept_16_7_4_13_1_1057 7 36 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 189 3 2 12 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 189 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 36 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4 36 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 189 3 1 12 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 189
  (Polychromatic418967fa.accept_29_2_7_15_1_10824 2 36 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 36 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 189)))))))))))))))))))))))))))))))))))) (allB_succ 35 189
  (allA_succ_of_accept 34 35 189 (accept_3_4 34 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 189 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 189 (accept_3_4 31 35 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 189
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 29 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 35 189 7 4 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 35 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 35 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 189 (accept_3_4 25 35 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231
  24 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 189
  (Polychromatic418967fa.accept_17_6_1_2_1_10823 23 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 189 (accept_3_4 22 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35
  189 7 3 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  35 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 35 189 (accept_3_4 19 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 35 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 35 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 189 (accept_3_4 16 35 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 189 (Polychromatic418967fa.accept_12_3_11_9_1_193
  15 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 35 189 7 2 5 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 189 (accept_3_4 13
  35 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 189
  (Polychromatic418967fa.accept_15_12_5_9_1_3234 12 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 35 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 189 (accept_3_4 10 35 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 35 189 (Polychromatic418967fa.accept_19_9_16_18_1_3887 9 35 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 189 7 1 5 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 189 (Polychromatic418967fa.accept_20_5_15_9_1_9446 5 35 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 189 (accept_3_4 4 35 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 35 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 189 (accept_3_4 1 35 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 189))))))))))))))))))))))))))))))))))) (allB_succ 34 189
  (allA_succ_of_accept 33 34 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 34 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 189 (accept_3_5 32 34 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 34 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  30 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 189 (accept_3_5 29
  34 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 28 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 34 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 189 (accept_3_5 26 34 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 34 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 189
  (Polychromatic418967fa.accept_20_4_14_9_1_10822 24 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 34 189 (accept_3_5 23 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  34 189 (Polychromatic418967fa.accept_13_9_8_7_1_1073 22 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 34 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 34 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 34 189 (accept_3_5 20 34 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 34 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 34 189
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 34 189 (accept_3_5 17 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  34 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 34 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 34 189 (accept_3_5 14 34 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 34 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 34 189
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 34 189 (accept_3_5 11 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  34 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 34 189 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 34 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 34 189 (accept_3_5 8 34 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 34 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 34 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 34 189 (accept_3_5 5 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 34
  189 (Polychromatic418967fa.accept_19_4_15_18_1_10821 4 34 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 34 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 189 (accept_3_5 2 34 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 189)))))))))))))))))))))))))))))))))) (allB_succ 33
  189 (allA_succ_of_accept 32 33 189 (Polychromatic418967fa.accept_19_13_14_18_1_6683 32 33 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 189
  (Polychromatic418967fa.accept_17_14_16_2_1_4553 31 33 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 189 3 10 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 189 (Polychromatic418967fa.accept_18_11_15_9_1_360 29 33 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 33 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 189 3 9 11 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 189
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 33 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 189 (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 33 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 189 3 8 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 189 (Polychromatic418967fa.accept_14_9_5_7_1_1251 23 33 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 189
  (Polychromatic418967fa.accept_17_5_16_2_1_7094 22 33 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 189 3 7 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 33 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 189 (Polychromatic418967fa.accept_16_3_1_13_1_4968 19 33
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 189 3 6 11 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 189
  (Polychromatic418967fa.accept_18_17_15_9_1_5542 17 33 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 33 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 189 3 5 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 189 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 33 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 189
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 33 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 189 3 4 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 189 (Polychromatic418967fa.accept_18_11_15_9_1_360 11 33 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 189 (Polychromatic418967fa.accept_15_10_3_9_1_3285 10 33
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 189 3 3 11 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 189
  (Polychromatic418967fa.accept_15_8_3_9_1_4220 8 33 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 189 (Polychromatic418967fa.accept_19_7_14_18_1_6654 7 33 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 189 3 2 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 189 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 33 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 33 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 189 3 1 11 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 189 (Polychromatic418967fa.accept_14_2_5_7_1_3767 2 33 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 189 (Polychromatic418967fa.accept_17_1_16_2_1_1404 1 33 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 189)))))))))))))))))))))))))))))))))
  (allB_succ 32 189 (allA_succ_of_accept 31 32 189 (accept_3_4 31 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 32 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 189 (accept_3_4 28 32 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 189 (Polychromatic418967fa.accept_10_7_2_9_1_775
  27 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 189
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 26 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 189 (accept_3_4 25 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 189 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 189 (accept_3_4 22 32 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 32 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 189
  (Polychromatic418967fa.accept_19_1_13_18_1_6700 20 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 189 (accept_3_4 19 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 189 (accept_3_4 16 32 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 189 (Polychromatic418967fa.accept_24_15_8_21_1_7258 15 32 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 189
  (Polychromatic418967fa.accept_13_1_6_7_1_550 14 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 189 (accept_3_4 13 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 189 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 189 (accept_3_4 10 32 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 32 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 189
  (Polychromatic418967fa.accept_15_8_2_9_1_3200 8 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 189 (accept_3_4 7 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 189 (accept_3_4 4 32 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 189 (Polychromatic418967fa.accept_14_3_4_7_1_175 3 32 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 189 (Polychromatic418967fa.accept_20_2_12_9_1_6435
  2 32 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 189 (accept_3_4 1 32
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 189)))))))))))))))))))))))))))))))) (allB_succ 31 189
  (allA_succ_of_accept 30 31 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 189 (accept_3_5 29 31 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  27 31 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 189 (accept_3_5 26
  31 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 25 31 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 189 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 31 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 189 (accept_3_5 23 31 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 189 (Polychromatic418967fa.accept_15_6_1_9_1_1476
  21 31 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 189 (accept_3_5 20
  31 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 189
  (Polychromatic418967fa.accept_16_3_15_13_1_2825 19 31 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 189 (accept_3_5 17 31 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 189 (Polychromatic418967fa.accept_10_5_1_9_1_791
  15 31 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 189 (accept_3_5 14
  31 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 189
  (Polychromatic418967fa.accept_19_13_12_18_1_2677 13 31 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 31 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 189 (accept_3_5 11 31 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 189
  (Polychromatic418967fa.accept_19_9_12_18_1_8099 9 31 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 189 (accept_3_5 8 31 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  189 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 31 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 189 (accept_3_5 5 31 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3
  31 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 189 (accept_3_5 2 31 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 189
  (Polychromatic418967fa.accept_19_1_12_18_1_10820 1 31 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 31 189))))))))))))))))))))))))))))))) (allB_succ 30 189 (allA_succ_of_accept 29 30 189
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 30 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 30 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 189 3 9 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 30 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 189
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 30 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 30 189 3 8 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 30 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 30 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 30 189 3 7 10 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 30 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 30 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 30 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 189 3 6 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 189 (Polychromatic418967fa.accept_16_1_14_13_1_3834 17 30
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 189
  (Polychromatic418967fa.accept_11_5_8_2_1_588 16 30 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 30 189 3 5 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 30 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 30 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 189 (Polychromatic418967fa.accept_20_13_10_9_1_5030 13 30
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 189 3 4 10 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 30 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 30 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 189 3 3 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 189 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 30 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 189
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 30 189 3 2 10 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 30 189 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 30 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 30 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 30 189 3 1 10 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 30 189
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 30 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 30 189 (Polychromatic418967fa.accept_16_1_14_13_1_3834 1 30 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 189)))))))))))))))))))))))))))))) (allB_succ 29 189 (allA_succ_of_accept
  28 29 189 (accept_3_4 28 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 189
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 189 (accept_3_4 25 29 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 189 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 29 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 189
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 189 (accept_3_4 22 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 189 (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 189 (accept_3_4 19 29 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 189 (Polychromatic418967fa.accept_22_18_7_13_1_10819 18 29 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 189
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 189 (accept_3_4 16 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 189 (accept_3_4 13 29 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 189 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 29 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 189
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 189 (accept_3_4 10 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 189 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 189 (accept_3_4 7 29 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 189 (Polychromatic418967fa.accept_14_6_1_7_1_2775 6 29 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 189
  (Polychromatic418967fa.accept_15_5_14_9_1_274 5 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 189 (accept_3_4 4 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 29 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 189 (accept_3_4 1 29 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 189))))))))))))))))))))))))))))) (allB_succ 28 189 (allA_succ_of_accept 27 28 189
  (Polychromatic418967fa.accept_10_7_8_9_1_785 27 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 189 (accept_3_5 26 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 28 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 189 (accept_3_5 23 28 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 189 (Polychromatic418967fa.accept_13_9_2_7_1_1083 22 28 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 28 189 7 3 4 27 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 28 189 (accept_3_5 20 28 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 189
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 189 (accept_3_5 17 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 189 (Polychromatic418967fa.accept_19_16_9_18_1_8127 16 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 28 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 189 7 2 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  28 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 189
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 189 (accept_3_5 11 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 189 (Polychromatic418967fa.accept_16_10_12_13_1_4950 10 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 28 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 189 (accept_3_5 8 28 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 28 189 7 1 4 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 28 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 28 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 189 (accept_3_5 5 28 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 4 28 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 189
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 3 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 189 (accept_3_5 2 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 189)))))))))))))))))))))))))))) (allB_succ 27 189 (allA_succ_of_accept 26 27 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 27 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 189 3 8 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 27 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 189 3 7 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 189 (Polychromatic418967fa.accept_14_6_13_7_1_2015 20 27 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 189 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 27 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 189 9 2 3 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 189
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 27 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 189 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 27 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 189 3 5 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 189
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 27 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 189 3 4 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 189 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 27 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 189 9 1 3 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 189
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 27 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 189 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 27 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 189 3 2 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 27 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 189
  (Polychromatic418967fa.accept_15_4_12_9_1_773 4 27 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 189 3 1 9 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 27 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 189))))))))))))))))))))))))))) (allB_succ 26
  189 (allA_succ_of_accept 25 26 189 (accept_3_4 25 26 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 26 189 (Polychromatic418967fa.accept_17_7_9_2_1_629 24 26 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 189 (accept_3_4 22 26 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 189 (Polychromatic418967fa.accept_15_6_11_9_1_3215 21 26 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 189
  (Polychromatic418967fa.accept_11_9_4_2_1_600 20 26 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 189 (accept_3_4 19 26 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 189 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 26 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 189 (accept_3_4 16 26 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 189
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 26 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 26 189 (accept_3_4 13 26 189 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 26 189 (Polychromatic418967fa.accept_16_12_10_13_1_1042 12 26 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 189 (accept_3_4 10 26 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 189 (Polychromatic418967fa.accept_11_9_4_2_1_600 9
  26 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 189
  (Polychromatic418967fa.accept_19_8_7_18_1_1595 8 26 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 189 (accept_3_4 7 26 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  189 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 26 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 189 (accept_3_4 4 26 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 189 (Polychromatic418967fa.accept_14_2_12_7_1_617 2
  26 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 189 (accept_3_4 1 26 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 189)))))))))))))))))))))))))) (allB_succ 25 189
  (allA_succ_of_accept 24 25 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 25 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 189 (accept_3_5 23 25 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 189 (Polychromatic418967fa.accept_10_1_5_9_1_157
  21 25 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 189 (accept_3_5 20
  25 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 189
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 25 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 189 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 25 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 189 (accept_3_5 17 25 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 189 (Polychromatic418967fa.accept_12_3_1_9_1_202
  15 25 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 189 (accept_3_5 14
  25 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 189
  (Polychromatic418967fa.accept_24_13_1_21_1_10818 13 25 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 25 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 189 (accept_3_5 11 25 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 25 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 189
  (Polychromatic418967fa.accept_19_9_6_18_1_730 9 25 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 189 (accept_3_5 8 25 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  189 (Polychromatic418967fa.accept_16_7_9_13_1_4948 7 25 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 189 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 25 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 189 (accept_3_5 5 25 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 25 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 189 (accept_3_5 2 25 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  189 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 25 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 189))))))))))))))))))))))))) (allB_succ 24 189 (allA_succ_of_accept 23 24 189
  (Polychromatic418967fa.accept_10_3_4_9_1_15 23 24 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 189 (Polychromatic418967fa.accept_13_9_11_7_1_1077 22 24 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 189 3 7 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 189 (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 24 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 189
  (Polychromatic418967fa.accept_16_3_8_13_1_3867 19 24 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 189 3 6 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 189 (Polychromatic418967fa.accept_13_4_11_7_1_558 17 24 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 189 (Polychromatic418967fa.accept_13_3_11_7_1_2488 16 24
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 24 189 3 5 8 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 24 189
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 24 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 189 (Polychromatic418967fa.accept_10_3_4_9_1_15 13 24 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 189 3 4 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 189 (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 24
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 189
  (Polychromatic418967fa.accept_19_10_5_18_1_10817 10 24 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 24 189 3 3 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 24 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 24 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 189 (Polychromatic418967fa.accept_18_7_6_9_1_4205 7
  24 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 189 3 2 8 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 189
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 24 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 189 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 24 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 189 3 1 8 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 189 (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 24 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 189
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 24 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 189)))))))))))))))))))))))) (allB_succ 23 189 (allA_succ_of_accept 22 23 189 (accept_3_4 22 23 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624
  21 23 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 189 (accept_3_4 19 23 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 23 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 189 (accept_3_4 16 23 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 23 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 189 (accept_3_4 13 23 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 189 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 23 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 189 (Polychromatic418967fa.accept_19_11_4_18_1_5226 11 23 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 189 (accept_3_4 10 23 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 189 (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 23 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 189
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 189 (accept_3_4 7 23 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 189 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 23 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 189 (accept_3_4 4 23 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 189 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 23 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 189 (accept_3_4 1 23 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 189))))))))))))))))))))))) (allB_succ 22 189
  (allA_succ_of_accept 21 22 189 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 22 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 189 (accept_3_5 20 22 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 22 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 22 189 (Polychromatic418967fa.accept_12_6_10_9_1_531
  18 22 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 189 (accept_3_5 17
  22 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 189
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 22 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 22 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 189 (accept_3_5 14 22 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 22 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 189 (Polychromatic418967fa.accept_18_12_4_9_1_5452
  12 22 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 189 (accept_3_5 11
  22 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 189
  (Polychromatic418967fa.accept_23_10_22_5_1_10816 10 22 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 22 189 (Polychromatic418967fa.accept_16_9_6_13_1_3831 9 22 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 189 (accept_3_5 8 22 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 22 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 22 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 22 189 (accept_3_5 5 22 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22
  189 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 22 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 22 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 189 (accept_3_5 2 22 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 189)))))))))))))))))))))) (allB_succ 21 189
  (allA_succ_of_accept 20 21 189 (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 21 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 189 (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 21 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 189 3 6 7 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 189
  (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 21 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 21 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 189 3 5 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 21 189 7 2 3 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 189 (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 21 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 189 3 4 7 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 189
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 21 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 189 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 21 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 189 3 3 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 189 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 21 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 189 7 1 3 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 21 189 3 2 7 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 189
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 21 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 189 (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 21 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 189 3 1 7 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 189 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 21 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 189
  (Polychromatic418967fa.accept_11_1_10_2_1_58 1 21 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 189))))))))))))))))))))) (allB_succ 20 189 (allA_succ_of_accept 19 20 189 (accept_3_4 19 20 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 20 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 20 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 20 189 (accept_3_4 16 20 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  20 189 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 20 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 20 189 (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 20 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 189 (accept_3_4 13 20 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 189 (Polychromatic418967fa.accept_15_12_5_9_1_3234 12 20
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 20 189 (accept_3_4 10 20 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  20 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 20 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 20 189 (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 20 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 189 (accept_3_4 7 20 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 189 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 20 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 189
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 189 (accept_3_4 4 20 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  189 (Polychromatic418967fa.accept_15_3_5_9_1_764 3 20 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 189 (Polychromatic418967fa.accept_19_2_1_18_1_2660 2 20 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 189 (accept_3_4 1 20 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 189)))))))))))))))))))) (allB_succ 19 189 (allA_succ_of_accept 18 19 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 189 (accept_3_5 17 19 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 19 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 189 (accept_3_5 14 19 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 189 (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 19 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 189
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 19 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 189 (accept_3_5 11 19 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 189 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 19 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 189 (accept_3_5 8 19 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 189 (Polychromatic418967fa.accept_22_7_19_13_1_10815 7 19 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 189 (accept_3_5 5 19 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 19 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 189 (accept_3_5 2 19 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 189 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 19 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 189))))))))))))))))))) (allB_succ 18 189 (allA_succ_of_accept 17
  18 189 (Polychromatic418967fa.accept_10_7_8_9_1_785 17 18 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 189 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 18 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 189 3 5 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 189 (Polychromatic418967fa.accept_10_4_8_9_1_784 14
  18 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 189
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 18 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 189 3 4 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 189 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 18 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 189 9 1 2 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 189
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 18 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 189 3 2 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 189 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 18 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 189
  (Polychromatic418967fa.accept_10_4_8_9_1_784 4 18 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 189 3 1 6 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 18 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 189 (Polychromatic418967fa.accept_10_1_8_9_1_787 1 18 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 189)))))))))))))))))) (allB_succ 17 189
  (allA_succ_of_accept 16 17 189 (accept_3_4 16 17 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 17 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 189 (accept_3_4 13 17 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 189 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 189
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 17 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 189 (accept_3_4 10 17 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 189 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 17 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 189 (accept_3_4 7 17 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 189 (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 17 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 189
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 5 17 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 189 (accept_3_4 4 17 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 17 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 189 (accept_3_4 1 17 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 189))))))))))))))))) (allB_succ 16 189 (allA_succ_of_accept 15 16 189
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 16 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 189 (accept_3_5 14 16 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 189 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 16 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 189 (accept_3_5 11 16 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 189 (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 16
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 189
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 16 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 189 (accept_3_5 8 16 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  189 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 189 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 16 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 189 (accept_3_5 5 16 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 189 (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 16 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 189 (Polychromatic418967fa.accept_10_3_6_9_1_779 3
  16 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 189 (accept_3_5 2 16 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 189)))))))))))))))) (allB_succ 15 189
  (allA_succ_of_accept 14 15 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 189 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 15 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 189 3 4 5 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 189
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 15 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 189 3 3 5 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 189 (Polychromatic418967fa.accept_13_8_2_7_1_2452 8 15 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 189
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 15 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 189 3 2 5 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 189 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 15 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 189 (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 15 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 189 3 1 5 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 189 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 15 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 189))))))))))))))) (allB_succ 14 189 (allA_succ_of_accept 13 14 189
  (accept_3_4 13 14 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 189
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 14 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 189 (accept_3_4 10 14 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 189 (Polychromatic418967fa.accept_23_9_14_5_1_10814 9 14 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 189 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8
  14 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 14 189 7 1 2 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 14 189
  (Polychromatic418967fa.accept_12_6_2_9_1_537 6 14 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 189 (accept_3_4 4 14 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 189
  (Polychromatic418967fa.accept_28_2_14_21_1_10813 2 14 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 14 189 (accept_3_4 1 14 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14
  189)))))))))))))) (allB_succ 13 189 (allA_succ_of_accept 12 13 189 (Polychromatic418967fa.accept_19_12_13_18_1_3886 12
  13 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 13 189 (accept_3_5 11 13
  189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 13 189 (Polychromatic418967fa.accept_6_4_1_3_1_77
  10 13 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 189
  (Polychromatic418967fa.accept_19_9_13_18_1_10812 9 13 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 13 189 (accept_3_5 8 13 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13
  189 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 13 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 13 189 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 13 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 13 189 (accept_3_5 5 13 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 13 189 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 13 189
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 13 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 13 189 (accept_3_5 2 13 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 13
  189 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 13 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 13 189))))))))))))) (allB_succ 12 189 (allA_succ_of_accept 11 12 189
  (Polychromatic418967fa.accept_10_1_2_9_1_152 11 12 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 189 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 12 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 189 3 3 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 189 (Polychromatic418967fa.accept_13_8_12_7_1_2442 8 12 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 189
  (Polychromatic418967fa.accept_10_7_2_9_1_775 7 12 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 189 3 2 4 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 189 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 12 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 189 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 12 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 189 3 1 4 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 189
  (Polychromatic418967fa.accept_14_2_12_7_1_617 2 12 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 189 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 12 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 189)))))))))))) (allB_succ 11 189 (allA_succ_of_accept 10 11 189
  (accept_3_4 10 11 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 189
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 11 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 189 (accept_3_4 7 11 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 189 (Polychromatic418967fa.accept_10_5_1_9_1_791 5
  11 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 189 (accept_3_4 4 11 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 189 (Polychromatic418967fa.accept_12_3_11_9_1_193 3
  11 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 189 (accept_3_4 1 11 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  189))))))))))) (allB_succ 10 189 (allA_succ_of_accept 9 10 189 (Polychromatic418967fa.accept_19_9_10_18_1_10811 9 10
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 189 (accept_3_5 8 10 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 189
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 10 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 189 (accept_3_5 5 10 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  189 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4 10 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 10 189 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 189 (accept_3_5 2 10 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 189 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10 189 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 189)))))))))) (allB_succ 9 189 (allA_succ_of_accept 8
  9 189 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 9 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 9 189 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 9 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 189 3 2 3 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 189 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 9
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 189
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 9 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 189 3 1 3 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 189 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 9 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 189 (Polychromatic418967fa.accept_16_1_9_13_1_1822 1 9 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 189))))))))) (allB_succ 8 189
  (allA_succ_of_accept 7 8 189 (accept_3_4 7 8 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 189
  (Polychromatic418967fa.accept_12_6_8_9_1_553 6 8 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 189 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 189 (accept_3_4 4 8 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 189 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 8 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 189 (Polychromatic418967fa.accept_13_2_8_7_1_2424 2
  8 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 189 (accept_3_4 1 8 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 189)))))))) (allB_succ 7 189 (allA_succ_of_accept 6 7 189
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 189 (accept_3_5 5 7 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 189
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 189 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 7 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 189 (accept_3_5 2 7 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 189 (Polychromatic418967fa.accept_15_1_7_9_1_20 1 7 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 189))))))) (allB_succ 6 189 (allA_succ_of_accept 5 6 189
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 6 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 189 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 6 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 189 3 1 2 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 189 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 6 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 189
  (Polychromatic418967fa.accept_13_1_6_7_1_550 1 6 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 189)))))) (allB_succ 5 189 (allA_succ_of_accept 4 5 189 (accept_3_4 4 5 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 189 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 5 189 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 189 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 189 (accept_3_4 1 5 189
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 189))))) (allB_succ 4 189 (allA_succ_of_accept 3 4 189
  (Polychromatic418967fa.accept_10_3_4_9_1_15 3 4 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 189 (accept_3_5 2 4 189 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 189
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 189)))) (allB_succ 3 189 (allA_succ_of_accept 2 3 189 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 189
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 189
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 3 189 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 189))) (allB_succ 2 189 (allA_succ_of_accept 1 2 189 (accept_3_4 1 2 189 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 189)) (allB_two
  189))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


