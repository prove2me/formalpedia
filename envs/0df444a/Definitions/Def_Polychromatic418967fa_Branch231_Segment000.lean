-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch231_Segment000
-- name    : Polychromatic418967fa_Branch231_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:36:50.008793+00:00
-- url     : https://prove2.me/theorems/6198139b-4882-42c5-962e-3de57b013f13
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

def Polychromatic418967fa.branch_231_segment_000 : allB 100 231 :=
  allB_succ 99 231 (allA_succ_of_accept 98 99 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 98 99 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 231
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 97 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 231 3 32 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 95 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 231 (Polychromatic418967fa.accept_15_4_9_6_1_627 94 99 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 231 3 31 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 92 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 231 (Polychromatic418967fa.accept_15_1_9_6_1_1323 91 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 231 3 30 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 231 (Polychromatic418967fa.accept_13_11_8_10_1_676
  89 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 99 231 11 8 9 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 99 231 3 29 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 99 231
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 86 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 99 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 85 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 231 3 28 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 231 (Polychromatic418967fa.accept_13_5_8_10_1_4363
  83 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 99 231
  (Polychromatic418967fa.accept_10_2_9_1_1_185 82 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 99 231 3 27 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 99 231 (Polychromatic418967fa.accept_13_2_8_10_1_1902 80 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 231 (Polychromatic418967fa.accept_15_4_9_6_1_627 79 99 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 99 231 3 26 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 99 231 11 7 9 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 99 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 76 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 99 231 3 25 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 99 231 (Polychromatic418967fa.accept_15_14_9_6_1_5093 74 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 231 (Polychromatic418967fa.accept_16_9_3_7_1_6883 73 99 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 231 3 24 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 231
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 71 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 99 231 (Polychromatic418967fa.accept_13_5_8_10_1_4363 70 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 99 231 3 23 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 99 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 68
  99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 231
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 67 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 99 231 33 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 99 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 65 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 231 (Polychromatic418967fa.accept_13_12_8_10_1_1879 64 99
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 231 3 21 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 231
  (Polychromatic418967fa.accept_10_2_9_1_1_185 62 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 231 (Polychromatic418967fa.accept_15_1_9_6_1_1323 61 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 99 231 3 20 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 99 231 (Polychromatic418967fa.accept_13_7_8_10_1_2663
  59 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 231
  (Polychromatic418967fa.accept_10_8_9_1_1_189 58 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 99 231 3 19 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 99 231 (Polychromatic418967fa.accept_13_4_8_10_1_671 56 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 99 231 11 5 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 99 231 3 18 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 231 (Polychromatic418967fa.accept_18_17_9_15_1_7268 53 99
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 52 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 231 3 17 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 50 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 231 (Polychromatic418967fa.accept_15_4_9_6_1_627 49 99 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 231 3 16 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 231
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 47 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 231 (Polychromatic418967fa.accept_13_7_8_10_1_2663 46 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 231 3 15 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 99 231 11 4 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 99 231 (Polychromatic418967fa.accept_13_4_8_10_1_671
  43 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 99 231 3 14 33 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 99 231
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 41 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 231 (Polychromatic418967fa.accept_18_4_9_15_1_3383 40 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 231 3 13 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 38
  99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 231
  (Polychromatic418967fa.accept_13_11_8_10_1_676 37 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 99 231 3 12 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 99 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 231 (Polychromatic418967fa.accept_14_6_1_7_1_2775 34 99 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 231 33 1 3 7 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 231
  (Polychromatic418967fa.accept_10_2_9_1_1_185 32 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 231 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 231 3 10 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 231 (Polychromatic418967fa.accept_15_14_9_6_1_5093
  29 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 28 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 99 231 3 9 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 99 231 (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 99 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 231 3 8 33 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 231
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 99 231 11 2 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 99 231 3 7 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 99 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 231 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 99 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 231 3 6 33 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 231
  (Polychromatic418967fa.accept_13_4_8_10_1_671 17 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 231 (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 231 3 5 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 231 (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 99 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 231
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 99 231 3 4 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 11 99 231 11 1 9 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 99 231 (Polychromatic418967fa.accept_16_10_3_7_1_8094 10 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 231 3 3 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 99 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 231
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 231 3 2 33 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 99 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 231 3 1 33 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 231
  (Polychromatic418967fa.accept_10_2_9_1_1_185 2 99 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 231 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 99 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  231 (allA_succ_of_accept 97 98 231 (accept_3_4 97 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 231 (Polychromatic418967fa.accept_20_16_18_11_1_9605 96 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 95 98 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 231 (accept_3_4 94 98 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 98 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 92 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 91 98 231 7 13 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 90 98 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 98 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 98 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 231 (accept_3_4 88 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 231
  (Polychromatic418967fa.accept_20_7_18_11_1_5080 87 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 98 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 86 98 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 98 231 (accept_3_4 85 98 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 98 231 7 12 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 98 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 98 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 231 (accept_3_4 82 98 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 231
  (Polychromatic418967fa.accept_22_14_10_11_1_7472 80 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 98 231 (accept_3_4 79 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 98 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 78 98 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 98 231 7 11 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 98 231 (accept_3_4 76 98 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 98 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 231 (accept_3_4 73 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 231 (Polychromatic418967fa.accept_23_3_6_1_1_13817 72 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 98 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 98 231 7 10 14 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 98 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 98 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 68 98 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 98 231 (accept_3_4 67 98 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 98 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 98 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 98 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 65
  98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 231 (accept_3_4 64 98
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 98 231 7 9 14 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 98 231
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 62 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 231 (accept_3_4 61 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 231 (Polychromatic418967fa.accept_13_8_7_10_1_4362 60 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 98 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 231 (accept_3_4 58 98 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 231 7 8 14 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 231 (accept_3_4 55 98 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 98 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 98 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 98 231 (accept_3_4 52 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  98 231 (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 98 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 50 98 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 98 231 7 7 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 98 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 48
  98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 98 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 98 231 (accept_3_4 46 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  98 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 98 231 (Polychromatic418967fa.accept_15_14_8_6_1_2133 44 98 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 98 231 (accept_3_4 43 98 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 231 7 6 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 231 (accept_3_4 40 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39
  98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 231 (accept_3_4 37 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 231 (Polychromatic418967fa.accept_20_16_18_11_1_9605 36 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 98 231 7 5 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 98 231 (accept_3_4 34 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 98 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 98 231 (accept_3_4 31 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 98 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 30
  98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 98 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 98 231 7 4 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 98 231 (Polychromatic418967fa.accept_16_11_2_7_1_3374 27 98 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 231 (Polychromatic418967fa.accept_17_9_13_10_1_1825 26 98
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 98 231 (accept_3_4 25 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 98 231
  (Polychromatic418967fa.accept_26_24_20_23_1_10132 24 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 98 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 231 (accept_3_4 22 98 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 98 231 7 3 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 98 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 98 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 98 231 (accept_3_4 19 98 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 98 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 98 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 98 231 (accept_3_4 16 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  98 231 (Polychromatic418967fa.accept_22_15_10_11_1_13816 15 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 98 231 7 2 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 98 231 (accept_3_4 13 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 98 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 98 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 231 (accept_3_4 10 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 231
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 8 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 98 231 7 1 14 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 98 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 98 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 98 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 231 (accept_3_4 4 98 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 98
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 231 (accept_3_4 1 98 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  231 (allA_succ_of_accept 96 97 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 96 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 231 (accept_3_5 95 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 93 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 97 231 (accept_3_5 92 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  97 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 91 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 231 (accept_3_5 89 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 97 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 231
  (Polychromatic418967fa.accept_13_9_6_10_1_666 87 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 97 231 (accept_3_5 86 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  97 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 85 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 97 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 84 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 231 (accept_3_5 83 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 231
  (Polychromatic418967fa.accept_12_9_1_3_1_350 81 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 97 231 (accept_3_5 80 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  97 231 (Polychromatic418967fa.accept_22_13_9_11_1_13815 79 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 231 (accept_3_5 77 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 97 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 75 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 97 231 (accept_3_5 74 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  97 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 231 (Polychromatic418967fa.accept_15_12_7_6_1_4013 72 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 231 (accept_3_5 71 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 231
  (Polychromatic418967fa.accept_12_9_1_3_1_350 69 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 231 (accept_3_5 68 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 231 (accept_3_5 65 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 231
  (Polychromatic418967fa.accept_19_6_2_3_1_11217 63 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 231 (accept_3_5 62 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 231 (Polychromatic418967fa.accept_13_9_6_10_1_666 61 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 231 (Polychromatic418967fa.accept_22_16_9_11_1_13814 60 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 231 (accept_3_5 59 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 231 (accept_3_5 56 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 231 (accept_3_5 53 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 231
  (Polychromatic418967fa.accept_13_12_6_10_1_667 51 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 231 (accept_3_5 50 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 231 (accept_3_5 47 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 231
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 231 (accept_3_5 44 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 231 (Polychromatic418967fa.accept_13_4_6_10_1_1199 43 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 231 (accept_3_5 41 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 231 (accept_3_5 38 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 231 (accept_3_5 35 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 231
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 231 (accept_3_5 32 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 231 (accept_3_5 29 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 231
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 231 (accept_3_5 26 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 231 (Polychromatic418967fa.accept_13_12_6_10_1_667 25 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 231 (accept_3_5 23 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 231 (accept_3_5 20 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 231 (accept_3_5 17 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 231
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 231 (accept_3_5 14 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 231 (accept_3_5 11 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 231
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 231 (accept_3_5 8 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  231 (Polychromatic418967fa.accept_25_7_22_6_1_13813 7 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 231 (accept_3_5 5 97 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 231 (accept_3_5 2 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 97 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 96 231 (allA_succ_of_accept 95 96 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 95 96 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 231
  (Polychromatic418967fa.accept_18_4_6_15_1_2250 94 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 96 231 3 31 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 92 96 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 92 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 231 (Polychromatic418967fa.accept_22_3_8_11_1_13812 91 96
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 231 3 30 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 231
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 89 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 231 (Polychromatic418967fa.accept_17_3_11_10_1_7787 88 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 96 231 3 29 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 96 231 (Polychromatic418967fa.accept_13_8_5_10_1_2701
  86 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 231
  (Polychromatic418967fa.accept_10_5_6_1_1_836 85 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 231 3 28 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 231 (Polychromatic418967fa.accept_18_11_6_15_1_5953 83 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 96 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 82 96 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 231 3 27 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 231
  (Polychromatic418967fa.accept_13_2_5_10_1_250 80 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 96 231 (Polychromatic418967fa.accept_14_9_12_7_1_597 79 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 231 3 26 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 231 (Polychromatic418967fa.accept_10_7_6_1_1_486 77
  96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 231
  (Polychromatic418967fa.accept_18_4_6_15_1_2250 76 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 96 231 3 25 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 96 231 (Polychromatic418967fa.accept_19_17_1_3_1_4160 74 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 231 (Polychromatic418967fa.accept_13_8_5_10_1_2701 73 96
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 231 3 24 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 231
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 71 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 231 (Polychromatic418967fa.accept_18_16_6_15_1_3376 70 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 96 231 3 23 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 96 231 (Polychromatic418967fa.accept_19_11_1_3_1_5555
  68 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 231
  (Polychromatic418967fa.accept_10_7_6_1_1_486 67 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 231 3 22 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 96 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 65 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 231 (Polychromatic418967fa.accept_18_10_6_15_1_3412 64 96
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 231 3 21 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 231
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 96 231 (Polychromatic418967fa.accept_14_5_12_7_1_2767 61 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 231 3 20 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 231 (Polychromatic418967fa.accept_18_5_6_15_1_3413
  59 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 231
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 58 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 96 231 3 19 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 96 231 (Polychromatic418967fa.accept_13_4_5_10_1_1247 56 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 96 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 231 3 18 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 231
  (Polychromatic418967fa.accept_18_17_6_15_1_8704 53 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 96 231 3 17 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 96 231
  (Polychromatic418967fa.accept_31_19_3_14_1_13811 50 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 96 231 (Polychromatic418967fa.accept_19_11_1_3_1_5555 49 96 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 231 3 16 32 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 231
  (Polychromatic418967fa.accept_10_7_6_1_1_486 47 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 231 (Polychromatic418967fa.accept_18_10_6_15_1_3412 46 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 231 3 15 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 231 (Polychromatic418967fa.accept_14_2_12_7_1_617
  44 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 231
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 43 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 231 3 14 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 231 (Polychromatic418967fa.accept_13_2_5_10_1_250 41 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 231 (Polychromatic418967fa.accept_18_4_6_15_1_2250 40 96
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 231 3 13 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 231
  (Polychromatic418967fa.accept_17_4_11_10_1_5167 38 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 231 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 231 3 12 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 35
  96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 231
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 34 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 96 231 3 11 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 96 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 231 (Polychromatic418967fa.accept_22_9_8_11_1_13810 31 96
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 231 3 10 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 231
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 29 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 231 (Polychromatic418967fa.accept_13_2_5_10_1_250 28 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 231 3 9 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 231 (Polychromatic418967fa.accept_20_6_16_11_1_2379 26 96
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 231
  (Polychromatic418967fa.accept_10_5_6_1_1_836 25 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 231 3 8 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 231 (Polychromatic418967fa.accept_14_9_12_7_1_597 23 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 96 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 231 3 7 32 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 231
  (Polychromatic418967fa.accept_17_3_11_10_1_7787 20 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 231 (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 231 3 6 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 231 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 96 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 231
  (Polychromatic418967fa.accept_14_2_12_7_1_617 16 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 96 231 3 5 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 96 231 (Polychromatic418967fa.accept_22_14_8_11_1_2777 14 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 231 (Polychromatic418967fa.accept_22_13_8_11_1_13809 13 96
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 231 3 4 32 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 231
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 11 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 231 (Polychromatic418967fa.accept_18_10_6_15_1_3412 10 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 231 3 3 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 231 (Polychromatic418967fa.accept_13_8_5_10_1_2701 8 96 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 231
  (Polychromatic418967fa.accept_10_7_6_1_1_486 7 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 231 3 2 32 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 231 (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 96 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 231 3 1 32 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 231
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 96 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 231 (Polychromatic418967fa.accept_17_1_11_10_1_5149 1 96 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 231
  (allA_succ_of_accept 94 95 231 (accept_3_4 94 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 93 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 231 (accept_3_4 91 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 231 (Polychromatic418967fa.accept_20_10_15_11_1_3759 90 95 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 89 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 231 (accept_3_4 88 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 231 (Polychromatic418967fa.accept_14_3_11_7_1_1260 87 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 231 (accept_3_4 85 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 83 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 231 (accept_3_4 82 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 231 (accept_3_4 79 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 231 (Polychromatic418967fa.accept_15_3_5_6_1_4005 78 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 231
  (Polychromatic418967fa.accept_24_5_23_15_1_5084 77 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 231 (accept_3_4 76 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 231 (accept_3_4 73 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 231 (Polychromatic418967fa.accept_13_7_4_10_1_2675 72 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 231 (accept_3_4 70 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 231 (accept_3_4 67 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 231 (accept_3_4 64 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 231 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 231 (accept_3_4 61 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 231 (Polychromatic418967fa.accept_13_8_4_10_1_4358 60 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 231
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 231 (accept_3_4 58 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 231 (accept_3_4 55 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 231 (accept_3_4 52 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 231 (Polychromatic418967fa.accept_16_3_15_7_1_3417 51 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 231 (accept_3_4 49 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 231 (accept_3_4 46 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 231 (accept_3_4 43 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 231 (Polychromatic418967fa.accept_15_12_5_6_1_2148 42 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 231
  (Polychromatic418967fa.accept_15_11_5_6_1_669 41 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 231 (accept_3_4 40 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 231 (accept_3_4 37 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 231 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 231 (accept_3_4 34 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 231 (accept_3_4 31 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 231 (accept_3_4 28 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 231 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 231 (accept_3_4 25 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 231
  (Polychromatic418967fa.accept_22_1_7_11_1_10772 23 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 231 (accept_3_4 22 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 231 (accept_3_4 19 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 231 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 231 (accept_3_4 16 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 231 (Polychromatic418967fa.accept_22_15_7_11_1_4305 15 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 231 (accept_3_4 13 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 231 (accept_3_4 10 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 231 (accept_3_4 7 95 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 231 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 95 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 231
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 231 (accept_3_4 4 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 95 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 95 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 231 (accept_3_4 1 95 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 231
  (allA_succ_of_accept 93 94 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 231 (accept_3_5 92 94 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  90 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 231 (accept_3_5 89
  94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 231
  (Polychromatic418967fa.accept_9_7_4_6_1_273 88 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 231 (Polychromatic418967fa.accept_10_7_4_1_1_1319 87 94 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 231 (accept_3_5 86 94 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 84
  94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 231 (accept_3_5 83 94
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 231 (Polychromatic418967fa.accept_9_1_4_6_1_5
  82 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 231 (accept_3_5 80 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 78 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 231 (accept_3_5 77 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 231 (Polychromatic418967fa.accept_13_11_3_10_1_4374 76 94
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 75 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 231 (accept_3_5 74 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 231 (Polychromatic418967fa.accept_13_7_3_10_1_656 72 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 231 (accept_3_5 71 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 231 (accept_3_5 68 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 231 (accept_3_5 65 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 231
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 231 (accept_3_5 62 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 231 (Polychromatic418967fa.accept_14_4_10_7_1_1946 60 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 231 (accept_3_5 59 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 231 (Polychromatic418967fa.accept_13_6_3_10_1_698 58 94 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 231 (accept_3_5 56 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 231 (accept_3_5 53 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 94 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 231
  (Polychromatic418967fa.accept_22_7_6_11_1_13808 51 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 231 (accept_3_5 50 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 231 (accept_3_5 47 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 231 (accept_3_5 44 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 231 (accept_3_5 41 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 231 (Polychromatic418967fa.accept_15_10_4_6_1_2129 40 94
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 231 (accept_3_5 38 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 231 (Polychromatic418967fa.accept_16_4_14_7_1_5641 36 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 231 (accept_3_5 35 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 94 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 231 (accept_3_5 32 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 231 (accept_3_5 29 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 231
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 231 (accept_3_5 26 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 231 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 231 (accept_3_5 23 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 231 (Polychromatic418967fa.accept_23_22_2_1_1_13807 22 94
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 231 (accept_3_5 20 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 231 (accept_3_5 17 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 94 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 231
  (Polychromatic418967fa.accept_10_5_4_1_1_842 15 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 231 (accept_3_5 14 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 231 (accept_3_5 11 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 94 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 231 (accept_3_5 8 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 94 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 231 (accept_3_5 5 94 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 231 (Polychromatic418967fa.accept_14_4_10_7_1_1946 4 94 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  94 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 231 (accept_3_5 2 94 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 231
  (allA_succ_of_accept 92 93 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 92 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 91 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 231 3 30 31 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 89 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 88 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 231 3 29 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 86
  93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 85 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 231 3 28 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 231 3 27 31 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 80 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 231 3 26 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 76 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 231 3 25 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 231 3 24 31 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 231 3 23 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 231 3 22 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 231 3 21 31 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 231 3 20 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 231 3 19 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 231 3 18 31 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 231 3 17 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 231 3 16 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 231 3 15 31 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 231 3 14 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 231 3 13 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 231 3 12 31 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 231 3 11 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 231 3 10 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 231 3 9 31 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 231 3 8 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 231 3 7 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 231 3 6 31 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 231 3 5 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 231 3 4 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 231 3 3 31 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 231 3 2 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 93 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 231 3 1 31 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 93 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 231
  (allA_succ_of_accept 91 92 231 (accept_3_4 91 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 231 (accept_3_4 88 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 231 (Polychromatic418967fa.accept_13_9_1_10_1_647 87 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 86 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 231 (accept_3_4 85 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 231 (accept_3_4 82 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 231 (Polychromatic418967fa.accept_19_5_16_3_1_1820 81 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 80 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 231 (accept_3_4 79 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 231 (accept_3_4 76 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 231
  (Polychromatic418967fa.accept_13_9_1_10_1_647 74 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 231 (accept_3_4 73 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 231 (Polychromatic418967fa.accept_15_12_2_6_1_2127 72 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 231 (accept_3_4 70 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 231 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 68 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 231 (accept_3_4 67 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 231 (accept_3_4 64 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 231 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 231 (accept_3_4 61 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 231 (Polychromatic418967fa.accept_22_16_4_11_1_12232 60 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 231 (accept_3_4 58 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 231 (accept_3_4 55 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 231 (accept_3_4 52 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 231 (accept_3_4 49 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 231 (accept_3_4 46 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 231 (Polychromatic418967fa.accept_22_1_4_11_1_13806 45 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 231 (accept_3_4 43 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 231 (accept_3_4 40 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 231
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 38 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 231 (accept_3_4 37 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 231 (accept_3_4 34 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 231 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 231 (accept_3_4 31 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 231 (accept_3_4 28 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 231 (accept_3_4 25 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 231 (Polychromatic418967fa.accept_13_11_1_10_1_648 24 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 231 (accept_3_4 22 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 231
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 231 (accept_3_4 19 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 231 (accept_3_4 16 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 231 (Polychromatic418967fa.accept_14_1_8_7_1_1253 15 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 231 (accept_3_4 13 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 231 (accept_3_4 10 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 231 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 92 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 231 (accept_3_4 7 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  231 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 231 (accept_3_4 4 92 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 92 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 231 (Polychromatic418967fa.accept_16_2_12_7_1_3410
  2 92 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 231 (accept_3_4 1 92
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 231
  (allA_succ_of_accept 90 91 231 (Polychromatic418967fa.accept_22_2_3_11_1_10709 90 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 231 (accept_3_5 89 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 231
  (Polychromatic418967fa.accept_22_21_3_11_1_9130 87 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 91 231 (accept_3_5 86 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  91 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 85 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 91 231 7 12 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 91 231 (accept_3_5 83 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 81 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 231 (accept_3_5 80 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 79
  91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 231
  (Polychromatic418967fa.accept_15_3_1_6_1_206 78 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 91 231 7 11 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 76 91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 231 (accept_3_5 74 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 231
  (Polychromatic418967fa.accept_19_16_15_3_1_8408 73 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 91 231 (Polychromatic418967fa.accept_17_4_6_10_1_5164 72 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 231 (accept_3_5 71 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 91 231 7 10 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 91 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 91 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 231 (accept_3_5 68 91 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 231 (accept_3_5 65 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 91 231 7 9 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 91 231 (accept_3_5 62 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 91 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 231 (accept_3_5 59 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 58
  91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 57 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 91 231 7 8 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 91 231 (Polychromatic418967fa.accept_15_10_1_6_1_3033 55 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 231 (Polychromatic418967fa.accept_15_9_1_6_1_657 54 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 231 (accept_3_5 53 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52
  91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 231
  (Polychromatic418967fa.accept_16_3_11_7_1_770 51 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 231 (accept_3_5 50 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 91
  231 7 7 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  91 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 91 231 (accept_3_5 47 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 231 (accept_3_5 44 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 43
  91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 91 231 7 6 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 91 231 (accept_3_5 41
  91 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 231
  (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 91 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 231 (accept_3_5 38 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 91 231 (Polychromatic418967fa.accept_15_7_1_6_1_6150 37 91 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 36
  91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 91 231 7 5 13 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 91 231
  (Polychromatic418967fa.accept_6_4_1_3_1_77 34 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 91 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 231 (accept_3_5 32 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 91 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 91 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 30
  91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 231 (accept_3_5 29 91
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 91 231 7 4 13 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 91 231
  (Polychromatic418967fa.accept_19_8_15_3_1_5546 27 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 231 (accept_3_5 26 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 231 (Polychromatic418967fa.accept_15_9_1_6_1_657 24 91 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 231 (accept_3_5 23 91 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 91 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 91 231 7 3 13 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 91 231 (accept_3_5 20 91 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 231 (Polychromatic418967fa.accept_16_3_11_7_1_770 19 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 231
  (Polychromatic418967fa.accept_15_3_1_6_1_206 18 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 231 (accept_3_5 17 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 231 (Polychromatic418967fa.accept_16_15_11_7_1_6951 15 91 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 91 231 7 2 13 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 91 231
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 91 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 231 (accept_3_5 11 91 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 91 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9
  91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 231 (accept_3_5 8 91 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 231 7 1 13 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 91 231 (Polychromatic418967fa.accept_23_6_22_1_1_13805
  6 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 231 (accept_3_5 5 91
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 231 (Polychromatic418967fa.accept_6_4_1_3_1_77
  4 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 231 (accept_3_5 2 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  231 (Polychromatic418967fa.accept_22_1_3_11_1_10754 1 91 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 231
  (allA_succ_of_accept 89 90 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 88 90 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 231 3 29 30 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 86 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 90 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 231 3 28 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 231 (Polychromatic418967fa.accept_14_13_6_7_1_2013
  83 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 82 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 90 231 3 27 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 90 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 80 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 231 (Polychromatic418967fa.accept_20_19_10_11_1_5107 79 90
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 231 3 26 30 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 231 3 25 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 74
  90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 231 3 24 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 231 (Polychromatic418967fa.accept_13_6_12_10_1_690 71 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 70 90 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 90 231 3 23 30 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 68 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 231 (Polychromatic418967fa.accept_13_2_12_10_1_2649 67 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 231 3 22 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 90
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 64 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 90 231 3 21 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 90 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 62 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 231 3 20 30 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 231
  (Polychromatic418967fa.accept_13_7_12_10_1_640 59 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 90 231 3 19 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 90 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 56
  90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 231
  (Polychromatic418967fa.accept_14_13_6_7_1_2013 55 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 231 3 18 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 90 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 90 231 3 17 30 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 90 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 50 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 231 3 16 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 231 (Polychromatic418967fa.accept_13_8_12_10_1_4414
  47 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 231 3 15 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 231 (Polychromatic418967fa.accept_14_1_6_7_1_1936 43 90 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 231 3 14 30 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 90 231 3 13 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 38
  90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 231 3 12 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 231 (Polychromatic418967fa.accept_13_9_12_10_1_242 35 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 90 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 231 3 11 30 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 231 (Polychromatic418967fa.accept_17_14_5_10_1_9052 31 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 231 3 10 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 90 231 3 9 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 90 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 231 3 8 30 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 231
  (Polychromatic418967fa.accept_20_3_10_11_1_12493 23 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 90 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 90 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 231 3 7 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 20
  90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 231
  (Polychromatic418967fa.accept_13_6_12_10_1_690 19 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 231 3 6 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 90 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 231 3 5 30 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 231 3 4 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 231 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 90
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 90 231 3 3 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 231 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 90 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 231 3 2 30 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 90 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 231 3 1 30 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 90 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 231 (allA_succ_of_accept 88 89 231 (accept_3_4 88 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 231 (Polychromatic418967fa.accept_19_11_13_3_1_9820 87 89 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 231 (accept_3_4 85 89 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 84
  89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 83 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 231 (accept_3_4 82 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 231 (accept_3_4 79 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 77 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 231 (accept_3_4 76 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 231 (accept_3_4 73 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 231 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 231
  (Polychromatic418967fa.accept_25_21_14_6_1_13804 71 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 89 231 (accept_3_4 70 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 89 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 89 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 89 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 231 (accept_3_4 67 89 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 231 (accept_3_4 64 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 231 (Polychromatic418967fa.accept_18_9_17_15_1_2267 63 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 231 (accept_3_4 61 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 231 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 231 (accept_3_4 58 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 231 (accept_3_4 55 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 231
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 53 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 231 (accept_3_4 52 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 231 (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 231 (accept_3_4 49 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 231 (accept_3_4 46 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 231 (accept_3_4 43 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 231 (accept_3_4 40 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 231 (accept_3_4 37 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 231 (Polychromatic418967fa.accept_22_14_1_11_1_9148 36 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 231 (accept_3_4 34 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 231 (accept_3_4 31 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 231 (accept_3_4 28 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 231 (accept_3_4 25 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 231 (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 231 (accept_3_4 22 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 231 (accept_3_4 19 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 231
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 231 (accept_3_4 16 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 231 (accept_3_4 13 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 231 (accept_3_4 10 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 231 (accept_3_4 7 89 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 231 (accept_3_4 4 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 89 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 231 (accept_3_4 1 89 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 231 (allA_succ_of_accept 87 88 231 (Polychromatic418967fa.accept_14_3_4_7_1_175 87 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 231 (accept_3_5 86 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 84 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 88 231 (accept_3_5 83 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  88 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 82 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 88 231 (Polychromatic418967fa.accept_14_11_4_7_1_609 81 88 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 231 (accept_3_5 80 88 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 78 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 88 231 11 7 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 76 88 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 76 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 231 (accept_3_5 74 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 73
  88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 231
  (Polychromatic418967fa.accept_19_15_12_3_1_11213 72 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 88 231 (accept_3_5 71 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 88 231 (Polychromatic418967fa.accept_19_13_12_3_1_5540 70 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 231 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 231 (accept_3_5 68 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 67
  88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 88 231 11 6 8 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 88 231 (accept_3_5 65
  88 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 231
  (Polychromatic418967fa.accept_9_1_7_6_1_75 64 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 88 231 (Polychromatic418967fa.accept_10_3_8_1_1_182 63 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 231 (accept_3_5 62 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 231 (Polychromatic418967fa.accept_16_12_8_7_1_4530
  60 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 231 (accept_3_5 59
  88 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 231
  (Polychromatic418967fa.accept_9_4_7_6_1_255 58 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 88 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 231 (accept_3_5 56 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 88 231 11 5 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 88 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 88 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 231 (accept_3_5 53 88 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 231 (Polychromatic418967fa.accept_14_10_4_7_1_1214 52 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 231
  (Polychromatic418967fa.accept_19_13_12_3_1_5540 51 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 231 (accept_3_5 50 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 88 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 231 (accept_3_5 47 88 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 231
  (Polychromatic418967fa.accept_14_3_4_7_1_175 45 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 88 231 11 4 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 231 (accept_3_5 41 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 40
  88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 231 (accept_3_5 38 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 231 (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 88 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 231 (accept_3_5 35 88 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 231 (Polychromatic418967fa.accept_15_4_13_6_1_642 34 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 88 231 11 3 8 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 88 231 (accept_3_5 32 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 231 (accept_3_5 29 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 231 (Polychromatic418967fa.accept_18_9_16_15_1_2241 27 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 231 (accept_3_5 26 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 231
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 231 (accept_3_5 23 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  231 11 2 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  88 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 88 231 (accept_3_5 20 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 231 (accept_3_5 17 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 231
  (Polychromatic418967fa.accept_27_16_7_15_1_13803 16 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 231 (Polychromatic418967fa.accept_16_15_8_7_1_3407 15 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 231 (accept_3_5 14 88 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 88 231 11 1 8 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 88 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 231 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 231 (accept_3_5 8 88 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 231 (accept_3_5 5 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  231 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 88 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 231 (accept_3_5 2 88 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 231
  (allA_succ_of_accept 86 87 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 86 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 231 (Polychromatic418967fa.accept_15_10_12_6_1_3000 85 87
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 231 3 28 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 231
  (Polychromatic418967fa.accept_17_15_2_10_1_9021 83 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327 82 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 231 3 27 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 231 (Polychromatic418967fa.accept_14_10_3_7_1_1975
  80 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 231
  (Polychromatic418967fa.accept_13_1_9_10_1_625 79 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 231 3 26 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 231 (Polychromatic418967fa.accept_13_12_9_10_1_1223 77 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 76 87 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 231 3 25 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 231
  (Polychromatic418967fa.accept_10_4_7_1_1_471 74 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 231 (Polychromatic418967fa.accept_22_7_21_11_1_10746 73 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 231 3 24 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 231 (Polychromatic418967fa.accept_13_6_9_10_1_1201
  71 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 231
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 70 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 231 3 23 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 231 (Polychromatic418967fa.accept_23_22_18_1_1_13802 68 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 231 (Polychromatic418967fa.accept_14_11_3_7_1_604 67 87 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 231 3 22 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 231
  (Polychromatic418967fa.accept_15_5_12_6_1_639 65 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 64 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 231 3 21 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 231 (Polychromatic418967fa.accept_15_2_12_6_1_3063
  62 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 231
  (Polychromatic418967fa.accept_19_4_11_3_1_13801 61 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 231 3 20 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 231 (Polychromatic418967fa.accept_17_8_2_10_1_2879 59 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 231 (Polychromatic418967fa.accept_13_6_9_10_1_1201 58 87
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 231 3 19 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 231
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 231 (Polychromatic418967fa.accept_15_10_12_6_1_3000 55 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 231 3 18 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 231 (Polychromatic418967fa.accept_13_1_9_10_1_625
  53 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 231
  (Polychromatic418967fa.accept_14_10_3_7_1_1975 52 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 231 3 17 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 231 (Polychromatic418967fa.accept_15_5_12_6_1_639 50 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 231 (Polychromatic418967fa.accept_17_15_2_10_1_9021 49 87
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 231 3 16 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 231
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 47 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 46 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 231 3 15 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 44
  87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 231
  (Polychromatic418967fa.accept_25_18_12_6_1_4717 43 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 231 3 14 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 231 (Polychromatic418967fa.accept_20_1_7_11_1_3673 41 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 231 (Polychromatic418967fa.accept_13_1_9_10_1_625 40 87 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 231 3 13 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 231
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 38 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 231 3 12 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 231 (Polychromatic418967fa.accept_15_5_12_6_1_639
  35 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 231
  (Polychromatic418967fa.accept_10_4_7_1_1_471 34 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 231 3 11 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 231 (Polychromatic418967fa.accept_13_6_9_10_1_1201 32 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 231 (Polychromatic418967fa.accept_19_12_11_3_1_8399 31 87
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 231 3 10 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 231
  (Polychromatic418967fa.accept_17_12_2_10_1_2862 29 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 231 (Polychromatic418967fa.accept_19_9_11_3_1_5580 28 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 231 3 9 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 87 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 231
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 231 3 8 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 231 (Polychromatic418967fa.accept_19_4_11_3_1_13801 23 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 87
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 231 3 7 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 231
  (Polychromatic418967fa.accept_15_5_12_6_1_639 20 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 231 (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 231 3 6 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 231 (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 87 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 231
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 231 3 5 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 231 (Polychromatic418967fa.accept_19_13_11_3_1_5465 13 87
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 231 3 4 29 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 231
  (Polychromatic418967fa.accept_14_11_3_7_1_604 11 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 231 (Polychromatic418967fa.accept_14_10_3_7_1_1975 10 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 231 3 3 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 231 (Polychromatic418967fa.accept_17_8_2_10_1_2879 8 87 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 231
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 231 3 2 29 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 231 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 87 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 231 3 1 29 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 231
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 87 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 231 (Polychromatic418967fa.accept_13_1_9_10_1_625 1 87 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 231
  (allA_succ_of_accept 85 86 231 (accept_3_4 85 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 231 (accept_3_4 82 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 80 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 231 (accept_3_4 79 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 78 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 231 (accept_3_4 76 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 74 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 231 (accept_3_4 73 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 231 (accept_3_4 70 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 231
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 68 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 231 (accept_3_4 67 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 231 (accept_3_4 64 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 63 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 62 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 231 (accept_3_4 61 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 231 (Polychromatic418967fa.accept_17_9_1_10_1_2859 60 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 231 (accept_3_4 58 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 231 (accept_3_4 55 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 231 (accept_3_4 52 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 231 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 231
  (Polychromatic418967fa.accept_13_11_8_10_1_676 50 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 231 (accept_3_4 49 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 231 (accept_3_4 46 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 231 (accept_3_4 43 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 231 (accept_3_4 40 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 231 (accept_3_4 37 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 231 (Polychromatic418967fa.accept_20_16_6_11_1_9657 36 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 231 (accept_3_4 34 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 231
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 231 (accept_3_4 31 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 231 (accept_3_4 28 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 231 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 231 (accept_3_4 25 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 231 (accept_3_4 22 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 231 (accept_3_4 19 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 231 (accept_3_4 16 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 231
  (Polychromatic418967fa.accept_17_14_1_10_1_3941 14 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 231 (accept_3_4 13 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 231 (accept_3_4 10 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 231 (accept_3_4 7 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 231 (accept_3_4 4 86 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 86 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  86 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 231 (accept_3_4 1 86 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 231
  (allA_succ_of_accept 84 85 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 84 85 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 231 (accept_3_5 83 85 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 231 (Polychromatic418967fa.accept_12_9_1_3_1_350
  81 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 231 (accept_3_5 80
  85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 231
  (Polychromatic418967fa.accept_9_7_4_6_1_273 79 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 231 (accept_3_5 77 85 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 75
  85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 231 (accept_3_5 74 85
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 231 (Polychromatic418967fa.accept_9_1_4_6_1_5
  73 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 231
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 72 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 231 (accept_3_5 71 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 231 (accept_3_5 68 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 231 (Polychromatic418967fa.accept_19_10_9_3_1_7009 67 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 231 (accept_3_5 65 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 231 (Polychromatic418967fa.accept_15_3_10_6_1_632 63 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 231 (accept_3_5 62 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 231
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 60 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 231 (accept_3_5 59 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 231 (accept_3_5 56 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 231 (accept_3_5 53 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 231 (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 231 (accept_3_5 50 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 85 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 231 (accept_3_5 47 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 231 (accept_3_5 44 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 231 (accept_3_5 41 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 231 (accept_3_5 38 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 231
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 231 (accept_3_5 35 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 231 (accept_3_5 32 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 231 (Polychromatic418967fa.accept_15_1_10_6_1_631 31 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 231 (accept_3_5 29 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 231 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 231 (accept_3_5 26 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 85 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 231
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 231 (accept_3_5 23 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 231 (accept_3_5 20 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 231 (accept_3_5 17 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 231 (Polychromatic418967fa.accept_19_15_9_3_1_13764 15 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 231 (accept_3_5 14 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 231 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 85
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 231 (accept_3_5 11 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 231 (accept_3_5 8 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 85 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 231 (accept_3_5 5 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 85 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 231 (accept_3_5 2 85 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 231
  (allA_succ_of_accept 83 84 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 82 84 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 231 3 27 28 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 80 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 231 3 26 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 84 231 7 11 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 84 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 76
  84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 84 231 3 25 28 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 84 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 74 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 84 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 231 3 24 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 71
  84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 231 7 10 12 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 84 231 3 23 28 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 68 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 84 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 231 3 22 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 65
  84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 64 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 84 231 21 3 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 84 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 62 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 84 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 231 3 20 28 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 58 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 84 231 3 19 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 84 231 7 8 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 55
  84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 231 3 18 28 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 231 3 17 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 84 231 7 7 12 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 84 231 3 16 28 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 231 3 15 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 43 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 231 21 2 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 84 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 84 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 84 231 3 13 28 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 84 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 84 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 231 3 12 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 84 231 7 5 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 84 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 34
  84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 231 3 11 28 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 231 3 10 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 231 7 4 12 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 84 231 3 9 28 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 231 3 8 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 84 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 84 231 21 1 4 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 84 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 84 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 231 3 6 28 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 231 3 5 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 231 7 2 12 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 84 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 231 3 4 28 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 231 3 3 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 84 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 84 231 7 1 12 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 84 231 3 2 28 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 84 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 231 3 1 28 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 84 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 84 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 231
  (allA_succ_of_accept 82 83 231 (accept_3_4 82 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 231 (accept_3_4 79 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316 78 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 77 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 231 (accept_3_4 76 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 231 (accept_3_4 73 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 231 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 71 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 231 (accept_3_4 70 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 231 (accept_3_4 67 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 231
  (Polychromatic418967fa.accept_31_3_21_14_1_13800 65 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 83 231 (accept_3_4 64 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 83 231 (Polychromatic418967fa.accept_16_15_3_7_1_3389 63 83 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 83 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 231 (accept_3_4 61 83 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 60
  83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 59 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 231 (accept_3_4 58 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 231 (accept_3_4 55 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 231 (Polychromatic418967fa.accept_13_2_5_10_1_250 54 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 231 (accept_3_4 52 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 231 (Polychromatic418967fa.accept_19_13_7_3_1_9798 51 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 231 (accept_3_4 49 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 231
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 47 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 231 (accept_3_4 46 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 231 (accept_3_4 43 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 231 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 231 (accept_3_4 40 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 231 (accept_3_4 37 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 231 (accept_3_4 34 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 231 (accept_3_4 31 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 231
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 231 (accept_3_4 28 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 231 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 231 (accept_3_4 25 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 231 (Polychromatic418967fa.accept_18_6_11_15_1_7255 24 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 231 (accept_3_4 22 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 231 (accept_3_4 19 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 231 (accept_3_4 16 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 231 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 231 (accept_3_4 13 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 231
  (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 231 (accept_3_4 10 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 231 (accept_3_4 7 83 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 231 (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 83 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 231 (accept_3_4 4 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 83 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 231 (accept_3_4 1 83 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 231 (allA_succ_of_accept 81 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 231 (accept_3_5 80 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 82 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 82 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 78 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 82 231 (accept_3_5 77 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  82 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 82 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 231 (accept_3_5 74 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 231
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 72 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 82 231 (accept_3_5 71 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  82 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 231 (accept_3_5 68 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 82 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 82 231 (accept_3_5 65 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  82 231 (Polychromatic418967fa.accept_17_13_14_10_1_1847 64 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 82 231 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 231 (accept_3_5 62 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 231
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 60 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 231 (accept_3_5 59 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 231 (accept_3_5 56 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 231 (accept_3_5 53 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 231 (Polychromatic418967fa.accept_14_9_12_7_1_597 51 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 231 (accept_3_5 50 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 231 (accept_3_5 47 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 231 (accept_3_5 44 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 231 (accept_3_5 41 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 231 (accept_3_5 38 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 231 (accept_3_5 35 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 231 (accept_3_5 32 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 231 (accept_3_5 29 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 231 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 231 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 231 (accept_3_5 26 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 231
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 231 (accept_3_5 23 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 231 (accept_3_5 20 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 231 (accept_3_5 17 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 231 (Polychromatic418967fa.accept_22_15_16_11_1_546 15 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 231 (accept_3_5 14 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 231 (accept_3_5 11 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 231 (Polychromatic418967fa.accept_23_10_13_1_1_12178 10 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 231 (accept_3_5 8 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 82 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 231 (accept_3_5 5 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  231 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 82 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 82 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 231 (accept_3_5 2 82 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 231
  (allA_succ_of_accept 80 81 231 (Polychromatic418967fa.accept_13_2_3_10_1_658 80 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 79 81 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 231 3 26 27 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 77 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 231 (Polychromatic418967fa.accept_13_11_3_10_1_4374 76 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 231 3 25 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 73 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 231 3 24 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 231 (Polychromatic418967fa.accept_12_11_9_3_1_792 71 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 231 3 23 27 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 231
  (Polychromatic418967fa.accept_20_8_1_11_1_5125 68 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 231 3 22 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 65
  81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 231
  (Polychromatic418967fa.accept_18_10_9_15_1_7267 64 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 231 3 21 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 81 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 231 3 20 27 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 59 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 231 3 19 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 231 (Polychromatic418967fa.accept_16_8_1_7_1_2355
  56 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 231 3 18 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 231 (Polychromatic418967fa.accept_14_10_11_7_1_1955 52 81
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 231 3 17 27 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 231 3 16 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 231 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 231 3 15 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 231 (Polychromatic418967fa.accept_19_6_5_3_1_11210 44 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 81 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 231 3 14 27 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 231 (Polychromatic418967fa.accept_16_8_1_7_1_2355 40 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 231 3 13 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 231 3 12 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 231 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 231 3 11 27 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 231
  (Polychromatic418967fa.accept_13_6_3_10_1_698 32 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 231 3 10 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 29
  81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 231
  (Polychromatic418967fa.accept_13_2_3_10_1_658 28 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 231 3 9 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 81 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 231 3 8 27 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 231 3 7 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 231 (Polychromatic418967fa.accept_13_7_3_10_1_656 20 81 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 231 3 6 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 231 (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 81
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 231 3 5 27 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 231 3 4 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 231 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 81 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 231 3 3 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 231 (Polychromatic418967fa.accept_16_8_1_7_1_2355 8 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 81 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 231 3 2 27 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 231 (Polychromatic418967fa.accept_14_4_11_7_1_1234 4 81 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 231 3 1 27 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 81 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 231
  (allA_succ_of_accept 79 80 231 (accept_3_4 79 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 231 (accept_3_4 76 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 80 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 231 (accept_3_4 73 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 231 (Polychromatic418967fa.accept_15_12_5_6_1_2148 72 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 231 (accept_3_4 70 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 231 (Polychromatic418967fa.accept_22_3_14_11_1_13799 69 80 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 68 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 231 (accept_3_4 67 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 231 (accept_3_4 64 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 231 (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 80 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 231
  (Polychromatic418967fa.accept_27_8_26_15_1_13798 62 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 80 231 (accept_3_4 61 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 80 231 (Polychromatic418967fa.accept_13_8_2_10_1_652 60 80 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 231 (accept_3_4 58 80 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 57
  80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 231 (accept_3_4 55 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 231 (accept_3_4 52 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 231 (Polychromatic418967fa.accept_13_12_2_10_1_2698 51 80 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 231 (accept_3_4 49 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 231 (accept_3_4 46 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 231 (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 80 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 231
  (Polychromatic418967fa.accept_13_5_2_10_1_248 44 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 231 (accept_3_4 43 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 231 (accept_3_4 40 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 80 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 231 (accept_3_4 37 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 231 (Polychromatic418967fa.accept_17_2_12_10_1_9034 36 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 231 (accept_3_4 34 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 231 (Polychromatic418967fa.accept_15_3_5_6_1_4005 33 80 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 231 (accept_3_4 31 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 231 (accept_3_4 28 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 231 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 80 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 231
  (Polychromatic418967fa.accept_15_11_5_6_1_669 26 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 231 (accept_3_4 25 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 231 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 231 (accept_3_4 22 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 80 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 231 (accept_3_4 19 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 231 (accept_3_4 16 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 231 (Polychromatic418967fa.accept_25_15_5_6_1_13797 15 80 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 231 (accept_3_4 13 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 231 (accept_3_4 10 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 231 (Polychromatic418967fa.accept_22_9_14_11_1_13796 9 80 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 231
  (Polychromatic418967fa.accept_13_8_2_10_1_652 8 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 231 (accept_3_4 7 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  231 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 80 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 231 (accept_3_4 4 80 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 80
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 231 (accept_3_4 1 80 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 231
  (allA_succ_of_accept 78 79 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 78 79 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 231 (accept_3_5 77 79 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 75
  79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 231 (accept_3_5 74 79
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 231 (Polychromatic418967fa.accept_9_1_7_6_1_75
  73 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 231
  (Polychromatic418967fa.accept_10_2_9_1_1_185 72 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 231 (accept_3_5 71 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 231 (accept_3_5 68 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 231 (accept_3_5 65 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 231 (Polychromatic418967fa.accept_13_11_1_10_1_648 63 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 231 (accept_3_5 62 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 231 (Polychromatic418967fa.accept_13_9_1_10_1_647 61 79 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 231
  (Polychromatic418967fa.accept_22_16_13_11_1_10775 60 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 79 231 (accept_3_5 59 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 79 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 79 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 231 (accept_3_5 56 79 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 55
  79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 231
  (Polychromatic418967fa.accept_14_12_9_7_1_2762 54 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 231 (accept_3_5 53 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 231 (Polychromatic418967fa.accept_16_3_15_7_1_3417 51 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 231 (accept_3_5 50 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 79 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 231 (accept_3_5 47 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 231 (accept_3_5 44 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 231 (Polychromatic418967fa.accept_13_4_1_10_1_693 43 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 231
  (Polychromatic418967fa.accept_10_2_9_1_1_185 42 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 231 (accept_3_5 41 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 231 (accept_3_5 38 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 231
  (Polychromatic418967fa.accept_22_14_13_11_1_12237 36 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 79 231 (accept_3_5 35 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 79 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 79 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 231 (accept_3_5 32 79 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 31
  79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 231 (accept_3_5 29 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 231 (Polychromatic418967fa.accept_16_11_15_7_1_5654 27 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 231 (accept_3_5 26 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 79 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 231
  (Polychromatic418967fa.accept_13_11_1_10_1_648 24 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 231 (accept_3_5 23 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 231 (accept_3_5 20 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 231
  (Polychromatic418967fa.accept_10_8_9_1_1_189 18 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 231 (accept_3_5 17 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 231 (accept_3_5 14 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 231 (accept_3_5 11 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 231 (accept_3_5 8 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 231 (Polychromatic418967fa.accept_27_7_25_15_1_13795 7 79 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 231
  (Polychromatic418967fa.accept_16_6_15_7_1_1510 6 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 231 (accept_3_5 5 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 79 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 231 (accept_3_5 2 79 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 79 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 231
  (allA_succ_of_accept 77 78 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 231 3 25 26 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 74 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 231 3 24 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 231 (Polychromatic418967fa.accept_14_1_8_7_1_1253
  71 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 70 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 231 3 23 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 68 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 231 (Polychromatic418967fa.accept_20_7_18_11_1_5080 67 78
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 231 3 22 26 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 64 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 231 3 21 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 62
  78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 231 3 20 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 231 (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 231 3 19 26 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 231 (Polychromatic418967fa.accept_14_13_8_7_1_1224 55 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 231 3 18 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 231 3 17 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 231 3 16 26 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 231
  (Polychromatic418967fa.accept_16_15_14_7_1_10555 47 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 78 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 78 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 231 3 15 26 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 44 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 78 231 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 231 3 14 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 78 231 3 13 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 78 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 231 3 12 26 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 231
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 35 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 78 231 3 11 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 78 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 32
  78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 231
  (Polychromatic418967fa.accept_15_1_3_6_1_621 31 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 231 3 10 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 231 3 9 26 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 78 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 231 3 8 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 231 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 78 231 3 7 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 78 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 78 231 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 231 3 6 26 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 78 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 78 231 3 5 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 78 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 231 3 4 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 231 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 231 3 3 26 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 78 231 (Polychromatic418967fa.accept_20_7_18_11_1_5080 7 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 231 3 2 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 78 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 78 231 3 1 26 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 78 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 78 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 231
  (allA_succ_of_accept 76 77 231 (accept_3_4 76 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 231 (accept_3_4 73 77 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 231 (Polychromatic418967fa.accept_13_7_12_10_1_640 72 77 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 77 231 7 10 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 77 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 77 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 231 (accept_3_4 67 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 77 231 11 6 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 77 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 65
  77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 77 231 (accept_3_4 64 77
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 77 231 7 9 11 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 77 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 77 231 (accept_3_4 61 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  77 231 (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 77 231 (Polychromatic418967fa.accept_13_7_12_10_1_640 59 77 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 231 (accept_3_4 58 77 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 77 231 7 8 11 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 77 231 11 5 7 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 77 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 77 231 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 77 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 231 (accept_3_4 52 77 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 77 231 (Polychromatic418967fa.accept_25_1_2_6_1_13794 51 77 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 77 231 7 7 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 77 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 77 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 231 (accept_3_4 46 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 77 231 (Polychromatic418967fa.accept_12_9_5_3_1_782
  45 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 77 231 11 4 7 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 77 231 (accept_3_4 43
  77 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 77 231 7 6 11 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 77 231
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 41 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 231 (accept_3_4 40 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 231 (accept_3_4 37 77 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 77 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 77 231 7 5 11 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 77 231 (accept_3_4 34 77 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 77 231 11 3 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 77 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 231 (accept_3_4 31 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 77 231 7 4 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 77 231 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 77 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 231 (accept_3_4 25 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 231 (Polychromatic418967fa.accept_10_4_7_1_1_471
  24 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 231
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 23 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 77 231 11 2 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 77 231 7 3 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 77 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 231 (accept_3_4 19 77 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 77 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 231 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 77 231 (accept_3_4 16 77
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 77 231
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 77 231 7 2 11 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 77 231 (accept_3_4 13 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  77 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 77 231 11 1 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 77 231 (accept_3_4 10 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 77 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 77 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 77 231 7 1 11 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 77 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 77 231 (Polychromatic418967fa.accept_19_5_1_3_1_8421 5 77 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 231 (accept_3_4 4 77 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 77 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 77 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 231 (accept_3_4 1 77 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 76 231
  (allA_succ_of_accept 75 76 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 76 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 231 (accept_3_5 74 76 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  72 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 231 (accept_3_5 71
  76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 231
  (Polychromatic418967fa.accept_9_7_4_6_1_273 70 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 76 231 (Polychromatic418967fa.accept_13_4_11_10_1_1226 69 76 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 231 (accept_3_5 68 76 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 66
  76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 231 (accept_3_5 65 76
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 231 (Polychromatic418967fa.accept_9_1_4_6_1_5
  64 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 231
  (Polychromatic418967fa.accept_15_3_1_6_1_206 63 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 231 (accept_3_5 62 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 231 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 76 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 231 (accept_3_5 59 76 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 231 (Polychromatic418967fa.accept_20_18_16_11_1_13777 58 76
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 231 (accept_3_5 56 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 231 (accept_3_5 53 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 76 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 51 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 231 (accept_3_5 50 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 231 (accept_3_5 47 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 76 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 231
  (Polychromatic418967fa.accept_10_5_6_1_1_836 45 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 231 (accept_3_5 44 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 231 (accept_3_5 41 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258 40 76 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 231 (accept_3_5 38 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 231 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 231 (accept_3_5 35 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 76 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 231
  (Polychromatic418967fa.accept_15_3_1_6_1_206 33 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 231 (accept_3_5 32 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 231 (accept_3_5 29 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 76 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 231 (accept_3_5 26 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 231 (Polychromatic418967fa.accept_15_9_1_6_1_657 24 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 231 (accept_3_5 23 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 76 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 231 (accept_3_5 20 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 231 (accept_3_5 17 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 76 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 231
  (Polychromatic418967fa.accept_10_5_6_1_1_836 15 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 231 (accept_3_5 14 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 231 (accept_3_5 11 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 76 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 231
  (Polychromatic418967fa.accept_15_9_1_6_1_657 9 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 231 (accept_3_5 8 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 76 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 231 (accept_3_5 5 76 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 231 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 76 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  76 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 231 (accept_3_5 2 76 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 231 (allA_succ_of_accept
  74 75 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 75 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 231 3 24 25 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 231 3 23 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 68
  75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 231 3 22 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 231 3 21 25 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 231 3 20 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 231 3 19 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 231 3 18 25 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 231 3 17 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 231 3 16 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 231 3 15 25 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 44 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 231 3 14 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 231 3 13 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 231 3 12 25 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 231 3 11 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 231 3 10 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 231 3 9 25 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 231 3 8 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 231 3 7 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 231 3 6 25 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 231 3 5 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 231 3 4 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 231 3 3 25 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 231 3 2 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 75 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 231 3 1 25 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 75 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 75 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 231 (allA_succ_of_accept
  73 74 231 (accept_3_4 73 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 231
  (Polychromatic418967fa.accept_17_4_6_10_1_5164 72 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 74 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 231 (accept_3_4 70 74 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 68
  74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 231 (accept_3_4 67 74
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 231
  (Polychromatic418967fa.accept_9_3_2_6_1_264 66 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 231 (accept_3_4 64 74 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 231 (Polychromatic418967fa.accept_17_12_6_10_1_7807 63 74 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 231 (accept_3_4 61 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 231 (Polychromatic418967fa.accept_25_10_24_6_1_13793 60 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 231 (accept_3_4 58 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 231
  (Polychromatic418967fa.accept_22_12_8_11_1_13774 56 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 74 231 (accept_3_4 55 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 74 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 74 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 231 (accept_3_4 52 74 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 231
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 51 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 74 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 50 74 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 231 (accept_3_4 49 74 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 74 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 74 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 47
  74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 231 (accept_3_4 46 74
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9
  45 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 231 (accept_3_4 43 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 231 (accept_3_4 40 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 74 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 231
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 38 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 231 (accept_3_4 37 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 231 (Polychromatic418967fa.accept_22_14_8_11_1_2777 36 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 231 (accept_3_4 34 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 231 (accept_3_4 31 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 231 (accept_3_4 28 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 231 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 74 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 231 (accept_3_4 25 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 231 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 231 (accept_3_4 22 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 231
  (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 231 (accept_3_4 19 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 231 (accept_3_4 16 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 74 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 231 (accept_3_4 13 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 231 (accept_3_4 10 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 231 (accept_3_4 7 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 231 (accept_3_4 4 74 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 74 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 231 (Polychromatic418967fa.accept_19_2_17_3_1_11224
  2 74 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 231 (accept_3_4 1 74
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 231 (allA_succ_of_accept
  72 73 231 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 231 (accept_3_5 71 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 73 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 231 (accept_3_5 68 73 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 67
  73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 231 (accept_3_5 65 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 63 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 231 (accept_3_5 62 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 73 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 231
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 60 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 231 (accept_3_5 59 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 231 (accept_3_5 56 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 231 (Polychromatic418967fa.accept_19_17_16_3_1_8401 55 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 231 (accept_3_5 53 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 231 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 231 (accept_3_5 50 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 73 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 231 (accept_3_5 47 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 231 (accept_3_5 44 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 231 (accept_3_5 41 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 231 (accept_3_5 38 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 37 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 231
  (Polychromatic418967fa.accept_19_17_16_3_1_8401 36 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 231 (accept_3_5 35 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 231 (accept_3_5 32 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 231 (accept_3_5 29 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 231 (Polychromatic418967fa.accept_22_5_7_11_1_7378 27 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 231 (accept_3_5 26 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 73 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 231
  (Polychromatic418967fa.accept_13_11_8_10_1_676 24 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 231 (accept_3_5 23 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 231 (accept_3_5 20 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 231 (Polychromatic418967fa.accept_15_4_13_6_1_642 19 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 231 (accept_3_5 17 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 231 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 231 (accept_3_5 14 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 73 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 231 (accept_3_5 11 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 231 (accept_3_5 8 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 231 (accept_3_5 5 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 231 (accept_3_5 2 73 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 231 (Polychromatic418967fa.accept_19_1_16_3_1_11223 1 73 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 231 (allA_succ_of_accept 71
  72 231 (Polychromatic418967fa.accept_22_5_6_11_1_12251 71 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 231 (Polychromatic418967fa.accept_15_10_12_6_1_3000 70 72 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 231 3 23 24 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 231
  (Polychromatic418967fa.accept_13_3_7_10_1_668 68 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327 67 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 231 3 22 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 231 (Polychromatic418967fa.accept_14_9_2_7_1_1242
  65 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 231
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 64 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 231 3 21 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 231 (Polychromatic418967fa.accept_15_2_12_6_1_3063 62 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 231 (Polychromatic418967fa.accept_14_5_2_7_1_2804 61 72 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 231 3 20 24 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 231
  (Polychromatic418967fa.accept_10_9_2_1_1_840 59 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 231 (Polychromatic418967fa.accept_23_12_3_1_1_13792 58 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 231 3 19 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 56
  72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 231
  (Polychromatic418967fa.accept_13_3_7_10_1_668 55 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 231 3 18 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 231 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 72
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 231 3 17 24 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 231
  (Polychromatic418967fa.accept_15_5_12_6_1_639 50 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 231 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 231 3 16 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 231 (Polychromatic418967fa.accept_13_8_7_10_1_4362
  47 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 231 3 15 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 231 (Polychromatic418967fa.accept_16_12_8_7_1_4530 44 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 231 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 72 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 231 3 14 24 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 231
  (Polychromatic418967fa.accept_16_9_8_7_1_4529 41 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 231 (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 231 3 13 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 231 (Polychromatic418967fa.accept_13_12_7_10_1_2662
  38 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 231
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 37 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 231 3 12 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 231 (Polychromatic418967fa.accept_15_5_12_6_1_639 35 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 231 (Polychromatic418967fa.accept_13_8_7_10_1_4362 34 72
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 231 3 11 24 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 231
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 32 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 231 (Polychromatic418967fa.accept_16_15_8_7_1_3407 31 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 231 3 10 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 231 (Polychromatic418967fa.accept_10_9_2_1_1_840 29
  72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 231
  (Polychromatic418967fa.accept_16_12_8_7_1_4530 28 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 231 3 9 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 231 (Polychromatic418967fa.accept_13_12_7_10_1_2662 25 72
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 231 3 8 24 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 231
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 231 3 7 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 231 (Polychromatic418967fa.accept_15_5_12_6_1_639 20 72 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 231
  (Polychromatic418967fa.accept_10_9_2_1_1_840 19 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 231 3 6 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 231 (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 72 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 231 3 5 24 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 231
  (Polychromatic418967fa.accept_25_14_22_6_1_13791 14 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 72 231 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 72 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 231 3 4 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 231 (Polychromatic418967fa.accept_17_11_4_10_1_6430
  11 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 231
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 231 3 3 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 231 (Polychromatic418967fa.accept_13_8_7_10_1_4362 8 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 72 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 231 3 2 24 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 231
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 5 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 231 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 72 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 231 3 1 24 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 231 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 72 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 231
  (Polychromatic418967fa.accept_16_1_8_7_1_3377 1 72 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 231
  (allA_succ_of_accept 70 71 231 (accept_3_4 70 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 231 (accept_3_4 67 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 65 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 231 (accept_3_4 64 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 231 (Polychromatic418967fa.accept_15_3_11_6_1_3083 63 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 231 (accept_3_4 61 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 231 (Polychromatic418967fa.accept_17_9_3_10_1_9070 60 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 231 (accept_3_4 58 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 231 (accept_3_4 55 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 231 (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 231
  (Polychromatic418967fa.accept_22_9_5_11_1_13790 53 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 231 (accept_3_4 52 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 231 (Polychromatic418967fa.accept_13_12_6_10_1_667 51 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 231 (accept_3_4 49 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 231 (accept_3_4 46 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 231 (accept_3_4 43 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 231 (Polychromatic418967fa.accept_13_3_6_10_1_2658 42 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 231 (accept_3_4 40 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 231 (accept_3_4 37 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 231 (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 231
  (Polychromatic418967fa.accept_13_9_6_10_1_666 35 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 231 (accept_3_4 34 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 231 (accept_3_4 31 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 231 (accept_3_4 28 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 231 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 231 (accept_3_4 25 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 231 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 231 (accept_3_4 22 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 231 (accept_3_4 19 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 231 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 231
  (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 231 (accept_3_4 16 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 231 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 231 (accept_3_4 13 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 231 (accept_3_4 10 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 231 (accept_3_4 7 71 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 231 (Polychromatic418967fa.accept_14_6_1_7_1_2775 6 71 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 231 (accept_3_4 4 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 71 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 231 (accept_3_4 1 71 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 231
  (allA_succ_of_accept 69 70 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 231 (accept_3_5 68 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 70 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 70 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 66
  70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 231 (accept_3_5 65 70
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 231 (Polychromatic418967fa.accept_9_1_7_6_1_75
  64 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 70 231 7 9 10 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 70 231 (accept_3_5 62
  70 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 70 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 70 231 (Polychromatic418967fa.accept_13_8_5_10_1_2701 60 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 231 (accept_3_5 59 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 70 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 70 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 231 7 8 10 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 231
  (Polychromatic418967fa.accept_6_1_4_3_1_14 55 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 70 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 231 (accept_3_5 53 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 70 231 (Polychromatic418967fa.accept_25_2_20_6_1_13789 52 70 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 231
  (Polychromatic418967fa.accept_22_7_4_11_1_9131 51 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 231 (accept_3_5 50 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 70
  231 7 7 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  70 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 70 231 (accept_3_5 47 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 70 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 231 (accept_3_5 44 70 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43
  70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 231 7 6 10 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 231 (accept_3_5 41
  70 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 231
  (Polychromatic418967fa.accept_9_4_7_6_1_255 40 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 70 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 231 (accept_3_5 38 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 70 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 231
  (Polychromatic418967fa.accept_25_11_20_6_1_13788 36 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 70 231 7 5 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 70 231 (Polychromatic418967fa.accept_13_8_5_10_1_2701 34 70 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 231 (accept_3_5 32 70
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 231 (Polychromatic418967fa.accept_6_1_4_3_1_14
  31 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 231 (accept_3_5 29 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70
  231 7 4 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  70 231 (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 70 231 (accept_3_5 26 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 70 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 231 (Polychromatic418967fa.accept_18_6_16_15_1_7287 24 70
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 231 (accept_3_5 23 70 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 22
  70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 70 231 7 3 10 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 70 231 (accept_3_5 20
  70 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 231
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 70 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 231 (accept_3_5 17 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 70 231 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 70 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 231 (Polychromatic418967fa.accept_13_2_5_10_1_250
  15 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 231 7 2 10 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 70 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 231 (accept_3_5 11 70 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 70 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 70 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 231 (accept_3_5 8 70 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 70 231 7 1 10 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 70 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6
  70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 231 (accept_3_5 5 70 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 4
  70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 231 (accept_3_5 2 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 231
  (allA_succ_of_accept 68 69 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 68 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 231 3 22 23 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 231 (Polychromatic418967fa.accept_14_8_13_7_1_2798 64 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 231 3 21 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 62
  69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 61 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 231 3 20 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 231 (Polychromatic418967fa.accept_12_11_9_3_1_792 59 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 231 3 19 23 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 231
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 56 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 231 3 18 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 53
  69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 231
  (Polychromatic418967fa.accept_10_2_9_1_1_185 52 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 231 3 17 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 231 3 16 23 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 47 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 231 3 15 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 231 (Polychromatic418967fa.accept_13_5_4_10_1_1244
  44 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 43 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 231 3 14 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 231 (Polychromatic418967fa.accept_13_1_4_10_1_622 40 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 231 3 13 23 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 231 3 12 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 35
  69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 231 3 11 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 231 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 231 3 10 23 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 231 3 9 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 231 3 8 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 231 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 231 3 7 23 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 231
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 20 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 231 3 6 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 231
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 231 3 5 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 231 3 4 23 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 231 3 3 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 231 3 2 23 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 231 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 69 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 231 3 1 23 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 69 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 231 (allA_succ_of_accept 67 68 231 (accept_3_4 67 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 68 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 68 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 231 (accept_3_4 64 68 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 231 (Polychromatic418967fa.accept_10_3_8_1_1_182
  63 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 62 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 231 (accept_3_4 61 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 231 (Polychromatic418967fa.accept_16_12_4_7_1_3391 60 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 231 (accept_3_4 58 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 68 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 231 (accept_3_4 55 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 231 (accept_3_4 52 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 68 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 231
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 50 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 231 (accept_3_4 49 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 231 (accept_3_4 46 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 231 (Polychromatic418967fa.accept_13_6_3_10_1_698 45 68 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 231 (accept_3_4 43 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 231 (accept_3_4 40 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 68 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 231 (accept_3_4 37 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 231 (Polychromatic418967fa.accept_22_14_2_11_1_13787 36 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 231 (accept_3_4 34 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 231 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 68 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 231
  (Polychromatic418967fa.accept_13_6_3_10_1_698 32 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 231 (accept_3_4 31 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 231 (accept_3_4 28 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 68 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 231 (accept_3_4 25 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 231 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 231 (accept_3_4 22 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 231 (accept_3_4 19 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 231 (accept_3_4 16 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 231 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 68 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 231
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 231 (accept_3_4 13 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 231 (accept_3_4 10 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 231 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 68 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 231 (accept_3_4 7 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  231 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 231 (accept_3_4 4 68 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 68 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  68 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 231 (accept_3_4 1 68 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 231 (allA_succ_of_accept 66 67
  231 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 231 (accept_3_5 65 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 231 (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 231 (accept_3_5 62 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 67 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 231 (accept_3_5 59 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 231 (accept_3_5 56 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 231
  (Polychromatic418967fa.accept_10_4_7_1_1_471 54 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 231 (accept_3_5 53 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 231 (Polychromatic418967fa.accept_13_12_2_10_1_2698 51 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 231 (accept_3_5 50 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 231 (Polychromatic418967fa.accept_19_11_10_3_1_2934 49 67
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 231 (accept_3_5 47 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 231 (accept_3_5 44 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 231
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 231 (accept_3_5 41 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 231 (accept_3_5 38 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 231 (accept_3_5 35 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 231 (accept_3_5 32 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 231 (Polychromatic418967fa.accept_13_5_2_10_1_248 31 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 231 (accept_3_5 29 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 231 (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 231 (accept_3_5 26 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 67 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 231
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 231 (accept_3_5 23 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 231 (accept_3_5 20 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 231
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 231 (accept_3_5 17 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 231 (Polychromatic418967fa.accept_16_15_3_7_1_3389 15 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 231 (accept_3_5 14 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 231 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 67 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 231 (accept_3_5 11 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 231 (accept_3_5 8 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 231
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 231 (accept_3_5 5 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 67 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 231 (accept_3_5 2 67 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 67 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 231 (allA_succ_of_accept 65 66
  231 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 231 3 21 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 62
  66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 231 3 20 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 59 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 58 66 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 231 3 19 22 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 66 231 11 5 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 66 231 3 18 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 66 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 66 231 3 17 22 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 66 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 50 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 66 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 231 3 16 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 47
  66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 66 231 3 15 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 66 231 11 4 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 231 3 14 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 66 231 3 13 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 66 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 231 3 12 22 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 231 33 1 2 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 66 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 231 3 10 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 66 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 231 3 9 22 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 66 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 231 3 8 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 66 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 231 11 2 6 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 66 231 3 7 22 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 231 3 6 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 231 3 5 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 231 3 4 22 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 66 231 11 1 6 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 66 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 66 231 3 3 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 66 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 66 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 231 3 2 22 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 66 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 66 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 231 3 1 22 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 66 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 66 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 231
  (allA_succ_of_accept 64 65 231 (accept_3_4 64 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 231 (Polychromatic418967fa.accept_15_3_5_6_1_4005 63 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 231 (accept_3_4 61 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 231 (Polychromatic418967fa.accept_18_6_11_15_1_7255 60 65 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 59 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 231 (accept_3_4 58 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 231 (accept_3_4 55 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 231 (accept_3_4 52 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 231 (Polychromatic418967fa.accept_19_13_8_3_1_2906 51 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 231 (accept_3_4 49 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 65 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 231
  (Polychromatic418967fa.accept_14_5_9_7_1_590 47 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 231 (accept_3_4 46 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 231 (accept_3_4 43 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 231 (accept_3_4 40 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 231 (accept_3_4 37 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 231 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 65 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 231 (accept_3_4 34 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 231 (accept_3_4 31 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 231
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 231 (accept_3_4 28 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 231 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 231 (accept_3_4 25 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 65 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 231 (accept_3_4 22 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 231 (accept_3_4 19 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 231 (accept_3_4 16 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 231 (Polychromatic418967fa.accept_19_15_8_3_1_13786 15 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 231 (accept_3_4 13 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 65 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 231
  (Polychromatic418967fa.accept_15_11_5_6_1_669 11 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 231 (accept_3_4 10 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 231 (accept_3_4 7 65 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 231 (accept_3_4 4 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 65 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 231 (accept_3_4 1 65 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 231
  (allA_succ_of_accept 63 64 231 (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 64 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 231 (accept_3_5 62 64 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 231
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 64 231 (accept_3_5 59 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  64 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 64 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 231 (accept_3_5 56 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 54 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 64 231 (accept_3_5 53 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  64 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 64 231 (Polychromatic418967fa.accept_19_13_7_3_1_9798 51 64 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 231 (accept_3_5 50 64 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 64 231 (accept_3_5 47 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  64 231 (Polychromatic418967fa.accept_13_7_12_10_1_640 46 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 64 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 231 (accept_3_5 44 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 64 231 (accept_3_5 41 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  64 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 64 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 231 (accept_3_5 38 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 231
  (Polychromatic418967fa.accept_22_14_20_11_1_12230 36 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 64 231 (accept_3_5 35 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 64 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 64 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 231 (Polychromatic418967fa.accept_13_7_12_10_1_640 33 64
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 231 (accept_3_5 32 64 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 231 (accept_3_5 29 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 231 (Polychromatic418967fa.accept_13_2_12_10_1_2649 28 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 231 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 231 (accept_3_5 26 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 231
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 64 231 (accept_3_5 23 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 64 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 64 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 231 (accept_3_5 20 64 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 231 (accept_3_5 17 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 231 (accept_3_5 14 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 231 (accept_3_5 11 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 231 (Polychromatic418967fa.accept_15_10_4_6_1_2129 10 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 231 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 231 (accept_3_5 8 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 231 (accept_3_5 5 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  231 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 64 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 64 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 231 (accept_3_5 2 64 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 231 (allA_succ_of_accept 62 63 231
  (Polychromatic418967fa.accept_10_2_3_1_1_481 62 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 231 (Polychromatic418967fa.accept_15_1_3_6_1_621 61 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 231 3 20 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 231 (Polychromatic418967fa.accept_16_11_15_7_1_5654
  59 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 231
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 58 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 231 3 19 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 63 231 7 8 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 63 231 (Polychromatic418967fa.accept_13_3_11_10_1_2647 55 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 231 3 18 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258
  53 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 231
  (Polychromatic418967fa.accept_10_2_3_1_1_481 52 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 63 231 3 17 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 63 231 (Polychromatic418967fa.accept_15_5_3_6_1_2128 50 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63 231 7 7 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 63 231 3 16 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 231 (Polychromatic418967fa.accept_13_8_11_10_1_636 47 63 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 231
  (Polychromatic418967fa.accept_15_1_3_6_1_621 46 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 63 231 3 15 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 231 (Polychromatic418967fa.accept_25_19_13_6_1_8479 44 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 231 (Polychromatic418967fa.accept_13_4_11_10_1_1226 43 63
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 231 21 2 3 11 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 231
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 41 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258 40 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 231 3 13 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316
  38 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 231
  (Polychromatic418967fa.accept_19_18_6_3_1_8405 37 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 231 3 12 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 63 231 7 5 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 63 231 (Polychromatic418967fa.accept_13_8_11_10_1_636 34 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 231 3 11 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 231 (Polychromatic418967fa.accept_10_2_3_1_1_481 32
  63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 231
  (Polychromatic418967fa.accept_15_1_3_6_1_621 31 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 231 3 10 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 231 (Polychromatic418967fa.accept_13_3_11_10_1_2647 29 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 231 7 4 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 63 231 3 9 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 231 (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 63 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 231
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 63 231 3 8 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 63 231 (Polychromatic418967fa.accept_17_6_12_10_1_7781 23 63 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 231
  (Polychromatic418967fa.accept_10_2_3_1_1_481 22 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 63 231 21 1 3 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 63 231 (Polychromatic418967fa.accept_15_5_3_6_1_2128 20 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 231 (Polychromatic418967fa.accept_16_3_15_7_1_3417 19 63
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 231 3 6 21 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 231
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 231 (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 231 3 5 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 63 231 7 2 9 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 63 231 (Polychromatic418967fa.accept_20_13_3_11_1_9586 13 63
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 231 3 4 21 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 231
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 231 (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 231 3 3 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 63 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 231 7 1 9 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 63 231 3 2 21 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 231
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 231 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 63 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 231 3 1 21 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 231 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 63 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 231
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 63 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 231 (allA_succ_of_accept
  61 62 231 (accept_3_4 61 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 231
  (Polychromatic418967fa.accept_22_16_18_11_1_12242 60 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 62 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 231 (accept_3_4 58 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 62 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 62 231 (accept_3_4 55 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  62 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 62 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 231 (accept_3_4 52 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 62 231 (Polychromatic418967fa.accept_22_7_18_11_1_13785 51 62 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 231 (accept_3_4 49 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 231 (accept_3_4 46 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 231
  (Polychromatic418967fa.accept_19_6_5_3_1_11210 44 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 231 (accept_3_4 43 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 231 (accept_3_4 40 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 62 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 231 (accept_3_4 37 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 231 (accept_3_4 34 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 231 (accept_3_4 31 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 231 (accept_3_4 28 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 231 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 62 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 231 (accept_3_4 25 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 231 (Polychromatic418967fa.accept_26_24_10_23_1_13784 24 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 231 (accept_3_4 22 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 231 (accept_3_4 19 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 231 (accept_3_4 16 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 231 (Polychromatic418967fa.accept_14_1_6_7_1_1936 15 62 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 231 (accept_3_4 13 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 231 (accept_3_4 10 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 231
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 231 (accept_3_4 7 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  231 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 62 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 231 (accept_3_4 4 62 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 62 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 62
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 231 (accept_3_4 1 62 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 231 (allA_succ_of_accept 60 61 231
  (Polychromatic418967fa.accept_22_16_17_11_1_13783 60 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 61 231 (accept_3_5 59 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 61 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 61 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 61 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 231 (accept_3_5 56 61 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 55
  61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 231 (accept_3_5 53 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 231 (Polychromatic418967fa.accept_13_12_9_10_1_1223 51 61 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 231 (accept_3_5 50 61 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 61 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 231 (accept_3_5 47 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 231 (accept_3_5 44 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 231 (Polychromatic418967fa.accept_25_18_11_6_1_13782 43 61 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 231 (accept_3_5 41 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 231 (accept_3_5 38 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 61 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 231
  (Polychromatic418967fa.accept_16_4_13_7_1_4522 36 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 231 (accept_3_5 35 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 231 (accept_3_5 32 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 61 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 231 (accept_3_5 29 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 231 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 231 (accept_3_5 26 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 231 (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 61 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 231
  (Polychromatic418967fa.accept_15_9_1_6_1_657 24 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 231 (accept_3_5 23 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 231 (accept_3_5 20 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 61 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 231 (accept_3_5 17 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 231 (Polychromatic418967fa.accept_22_15_17_11_1_10729 15 61 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 231 (accept_3_5 14 61 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 61 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 231 (accept_3_5 11 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 231 (accept_3_5 8 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 231 (Polychromatic418967fa.accept_15_7_1_6_1_6150 7 61 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 231 (accept_3_5 5 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 61 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 231 (accept_3_5 2 61 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 61 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 231 (allA_succ_of_accept 59 60 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 60 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 231
  (Polychromatic418967fa.accept_18_4_6_15_1_2250 58 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 231 3 19 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 231 (Polychromatic418967fa.accept_13_4_8_10_1_671 56 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 231 (Polychromatic418967fa.accept_23_9_14_1_1_8977 55 60
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 231 3 18 20 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 231
  (Polychromatic418967fa.accept_14_11_4_7_1_609 53 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 231 (Polychromatic418967fa.accept_14_10_4_7_1_1214 52 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 231 3 17 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 231 (Polychromatic418967fa.accept_13_11_8_10_1_676
  50 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 231
  (Polychromatic418967fa.accept_22_5_16_11_1_13781 49 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 60 231 3 16 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 60 231 (Polychromatic418967fa.accept_17_13_9_10_1_2888 47 60 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 231
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 46 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 60 231 3 15 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 60 231 (Polychromatic418967fa.accept_13_5_8_10_1_4363 44 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 60 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 231 3 14 20 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 231
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 41 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 60 231 (Polychromatic418967fa.accept_16_8_12_7_1_2399 40 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 60 231 3 13 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 60 231 (Polychromatic418967fa.accept_13_12_8_10_1_1879
  38 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 231
  (Polychromatic418967fa.accept_13_11_8_10_1_676 37 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 60 231 3 12 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 60 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 231 (Polychromatic418967fa.accept_16_2_12_7_1_3410 34 60
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 231 3 11 20 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 231
  (Polychromatic418967fa.accept_23_9_14_1_1_8977 32 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 231 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 231 3 10 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 231 (Polychromatic418967fa.accept_18_11_6_15_1_5953
  29 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 231
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 60 231 3 9 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 60 231 (Polychromatic418967fa.accept_22_4_16_11_1_4197 26 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 231 (Polychromatic418967fa.accept_13_12_8_10_1_1879 25 60
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 231 3 8 20 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 231
  (Polychromatic418967fa.accept_18_5_6_15_1_3413 23 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 231 (Polychromatic418967fa.accept_18_4_6_15_1_2250 22 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 231 3 7 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 60 231 (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 60 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 231 3 6 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 231 (Polychromatic418967fa.accept_13_4_8_10_1_671 17 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 231 (Polychromatic418967fa.accept_17_16_9_10_1_3962 16 60
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 231 3 5 20 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 231
  (Polychromatic418967fa.accept_27_14_6_15_1_13780 14 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 60 231 (Polychromatic418967fa.accept_17_13_9_10_1_2888 13 60 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 231 3 4 20 77 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 231 (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 231 3 3 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 231 (Polychromatic418967fa.accept_16_8_12_7_1_2399 8 60 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 231
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 231 3 2 20 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 231 (Polychromatic418967fa.accept_13_5_8_10_1_4363 5 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 231 (Polychromatic418967fa.accept_13_4_8_10_1_671 4 60 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 231 3 1 20 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 231
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 2 60 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 231 (Polychromatic418967fa.accept_17_1_9_10_1_1864 1 60 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 231 (allA_succ_of_accept 58 59 231 (accept_3_4 58 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 59 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 59 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 59 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 231 (accept_3_4 55 59 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 231 (Polychromatic418967fa.accept_15_9_14_6_1_3004
  54 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 231 (accept_3_4 52 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 231 (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 231 (accept_3_4 49 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 59 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 231 (accept_3_4 46 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 231 (accept_3_4 43 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 231 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 59 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 231
  (Polychromatic418967fa.accept_23_18_13_1_1_13779 41 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 59 231 (accept_3_4 40 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 59 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 59 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 59 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 231 (accept_3_4 37 59 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 36
  59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 231 (accept_3_4 34 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 231 (accept_3_4 31 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 59 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 231 (accept_3_4 28 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 231 (Polychromatic418967fa.accept_18_9_5_15_1_2246 27 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 231 (accept_3_4 25 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 231 (Polychromatic418967fa.accept_14_10_3_7_1_1975 24 59 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 231
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 23 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 231 (accept_3_4 22 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 231 (accept_3_4 19 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 231 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 59 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 231 (accept_3_4 16 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 231 (accept_3_4 13 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 231 (accept_3_4 10 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 231 (accept_3_4 7 59 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 231 (Polychromatic418967fa.accept_18_6_5_15_1_7292 6 59 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 231 (accept_3_4 4 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 59 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 231 (accept_3_4 1 59 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 231
  (allA_succ_of_accept 57 58 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 231 (accept_3_5 56 58 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 58 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  54 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 231 (accept_3_5 53
  58 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 231
  (Polychromatic418967fa.accept_9_7_4_6_1_273 52 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 231 (Polychromatic418967fa.accept_13_12_6_10_1_667 51 58 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 231 (accept_3_5 50 58 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 48
  58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 231 (accept_3_5 47 58
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 231 (Polychromatic418967fa.accept_9_1_4_6_1_5
  46 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 231 (accept_3_5 44 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 58 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 231 (accept_3_5 41 58 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 231 (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 58
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 231 (accept_3_5 38 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 231 (Polychromatic418967fa.accept_19_17_1_3_1_4160 36 58 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 231 (accept_3_5 35 58 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 58 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 231 (accept_3_5 32 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 58 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 231 (accept_3_5 29 58 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 58 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 231
  (Polychromatic418967fa.accept_18_9_4_15_1_555 27 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 231 (accept_3_5 26 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 231 (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 58 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 231 (accept_3_5 23 58 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 231 (Polychromatic418967fa.accept_13_9_6_10_1_666 22 58 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 231 (accept_3_5 20 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 58 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 231 (accept_3_5 17 58 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 58 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 231
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 231 (accept_3_5 14 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 58 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 231 (accept_3_5 11 58 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 58 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 231 (accept_3_5 8 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 58 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 231 (accept_3_5 5 58 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 231 (Polychromatic418967fa.accept_13_4_6_10_1_1199 4 58 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  58 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 231 (accept_3_5 2 58 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 231 (allA_succ_of_accept 56 57 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 231 3 18 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 231 3 17 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 231 3 16 19 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 231 3 15 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 231 3 14 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 57 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 231 3 13 19 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 231 3 12 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 231 3 11 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 57 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 231 3 10 19 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 231 3 9 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 231 3 8 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 231 3 7 19 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 231 3 6 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 57 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 231 3 5 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 57 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 231 3 4 19 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 231 3 3 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 231 3 2 19 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 57 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 231 3 1 19 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 231))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 231 (allA_succ_of_accept 55 56 231 (accept_3_4 55 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 56 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 231 (accept_3_4 52 56 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 231
  (Polychromatic418967fa.accept_22_7_12_11_1_13778 51 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 56 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 50 56 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 56 231 7 7 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 56 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 48
  56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 56 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 56 231 (accept_3_4 46 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  56 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 56 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 56 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 56 231 (accept_3_4 43 56 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 231 7 6 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 56 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 231 (accept_3_4 40 56 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 231
  (Polychromatic418967fa.accept_20_18_16_11_1_13777 38 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 56 231 (accept_3_4 37 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 56 231 (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 56 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 56 231 7 5 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 56 231 (accept_3_4 34 56 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 56 231 (Polychromatic418967fa.accept_13_7_4_10_1_2675 33 56 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 231 (accept_3_4 31 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 231 7 4 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 231 (Polychromatic418967fa.accept_10_7_6_1_1_486 27
  56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 231 (accept_3_4 25 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 231 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 231 (accept_3_4 22 56 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 56 231 7 3 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 56 231 (Polychromatic418967fa.accept_13_7_4_10_1_2675 20 56 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 231 (accept_3_4 19 56 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 56 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 56 231 (accept_3_4 16 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  56 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 56 231 7 2 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 56 231 (accept_3_4 13 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 56 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 56 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 231 (accept_3_4 10 56 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 231 (Polychromatic418967fa.accept_15_9_11_6_1_637 9
  56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 56 231 7 1 8 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 56 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 56 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 231 (accept_3_4 4 56 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 231
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 231 (accept_3_4 1 56 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  231)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 231 (allA_succ_of_accept 54 55 231
  (Polychromatic418967fa.accept_10_4_5_1_1_497 54 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 231 (accept_3_5 53 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 231 (Polychromatic418967fa.accept_23_5_9_1_1_13776 51 55 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 231 (accept_3_5 50 55 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 55 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 231 (accept_3_5 47 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 55 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 55 231 11 4 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 55 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 43
  55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 231
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 42 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 231 (accept_3_5 41 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 55 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 231 (accept_3_5 38 55 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 231 (Polychromatic418967fa.accept_13_11_3_10_1_4374 37 55 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 231
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 231 (accept_3_5 35 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 55 231 11 3 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 55 231 (accept_3_5 32 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 55 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 55 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 55 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 231 (accept_3_5 29 55 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 231
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 231 (accept_3_5 26 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 55 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 231 (accept_3_5 23 55 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 55 231 11 2 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 55 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 55 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 231 (accept_3_5 20 55 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 55 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 231
  (Polychromatic418967fa.accept_15_3_10_6_1_632 18 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 231 (accept_3_5 17 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 231 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 55 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 231 (accept_3_5 14 55 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 55 231 11 1 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 10 55 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 55 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 55 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 231 (accept_3_5 8 55 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 7
  55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 231
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 231 (accept_3_5 5 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 231 (accept_3_5 2 55 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 231 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 55 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 231)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 231 (allA_succ_of_accept 53 54 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 54 231 3 17 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 54 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 231 3 16 18 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 231
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 231 3 15 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 44
  54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 231
  (Polychromatic418967fa.accept_17_9_3_10_1_9070 43 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 231 3 14 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 54 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 231 3 13 18 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 231 3 12 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 35
  54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 54 231 3 11 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 54 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 231 (Polychromatic418967fa.accept_13_5_2_10_1_248 31 54 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 231 3 10 18 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 231 3 9 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 54 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 231 3 8 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 231 (Polychromatic418967fa.accept_14_9_12_7_1_597 23 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 54 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 231 3 7 18 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 231 (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 231 3 6 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 231
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 54 231 3 5 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 54 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 231 3 4 18 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 231
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 231 3 3 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 54 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 231
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 231 3 2 18 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 54 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 231 3 1 18 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 54 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 231)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  231 (allA_succ_of_accept 52 53 231 (accept_3_4 52 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 231 (Polychromatic418967fa.accept_25_1_3_6_1_13775 51 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 231 (accept_3_4 49 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 53 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 231 (accept_3_4 46 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 231 (accept_3_4 43 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 231 (accept_3_4 40 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 231 (accept_3_4 37 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 231 (Polychromatic418967fa.accept_19_17_15_3_1_4174 36 53 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 231
  (Polychromatic418967fa.accept_13_9_1_10_1_647 35 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 231 (accept_3_4 34 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 231 (accept_3_4 31 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 231 (accept_3_4 28 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 231 (Polychromatic418967fa.accept_16_11_5_7_1_2395 27 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 231 (accept_3_4 25 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 231 (Polychromatic418967fa.accept_13_11_1_10_1_648 24 53 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 231 (accept_3_4 22 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 231 (accept_3_4 19 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 231
  (Polychromatic418967fa.accept_13_4_1_10_1_693 17 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 231 (accept_3_4 16 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 231 (Polychromatic418967fa.accept_17_15_2_10_1_9021 15 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 231 (accept_3_4 13 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 53 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 231 (accept_3_4 10 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 231 (accept_3_4 7 53 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 231 (accept_3_4 4 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 53 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 231 (accept_3_4 1 53 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 231))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 231
  (allA_succ_of_accept 51 52 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 52 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 231 (accept_3_5 50 52 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 48
  52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 231 (accept_3_5 47 52
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 231 (Polychromatic418967fa.accept_9_1_7_6_1_75
  46 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 52 231
  (Polychromatic418967fa.accept_14_3_10_7_1_3773 45 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 52 231 (accept_3_5 44 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  52 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 52 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 231 (accept_3_5 41 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 52 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 231 (accept_3_5 38 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 231 (accept_3_5 35 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 231 (Polychromatic418967fa.accept_22_12_8_11_1_13774 34 52 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 231
  (Polychromatic418967fa.accept_10_3_2_1_1_839 33 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 231 (accept_3_5 32 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 231 (accept_3_5 29 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 52 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 231 (accept_3_5 26 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  52 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 52 231 (Polychromatic418967fa.accept_16_8_4_7_1_3390 24 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 231 (accept_3_5 23 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 52 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 231 (accept_3_5 20 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 231 (accept_3_5 17 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 52 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 231
  (Polychromatic418967fa.accept_23_15_6_1_1_10656 15 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 231 (accept_3_5 14 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 231 (accept_3_5 11 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 52 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 231
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 231 (accept_3_5 8 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 52 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 52 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 231 (accept_3_5 5 52 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 52 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 52 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  52 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 231 (accept_3_5 2 52 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  231)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 231 (allA_succ_of_accept 50 51 231
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 50 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 51 231 (Polychromatic418967fa.accept_19_11_13_3_1_9820 49 51 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 231 3 16 17 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 231
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 47 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 51 231 (Polychromatic418967fa.accept_13_7_12_10_1_640 46 51 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 231 3 15 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 44
  51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 231
  (Polychromatic418967fa.accept_16_11_3_7_1_2375 43 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 51 231 3 14 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 51 231 (Polychromatic418967fa.accept_13_2_12_10_1_2649 41 51 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 231 (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 51
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 231 3 13 17 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 231
  (Polychromatic418967fa.accept_22_16_7_11_1_13773 38 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 51 231 (Polychromatic418967fa.accept_13_11_12_10_1_2652 37 51 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 231 3 12 17 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 231
  (Polychromatic418967fa.accept_13_9_12_10_1_242 35 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 231 (Polychromatic418967fa.accept_13_8_12_10_1_4414 34 51 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 231 3 11 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 231 (Polychromatic418967fa.accept_13_6_12_10_1_690
  32 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 231
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 31 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 231 3 10 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 231 (Polychromatic418967fa.accept_19_10_13_3_1_13772 29 51 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 51 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 231 3 9 17 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 231
  (Polychromatic418967fa.accept_14_12_9_7_1_2762 26 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 231 (Polychromatic418967fa.accept_16_9_3_7_1_6883 25 51 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 231 3 8 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 231 (Polychromatic418967fa.accept_19_4_13_3_1_5571 23 51 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 231
  (Polychromatic418967fa.accept_13_9_12_10_1_242 22 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 231 3 7 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 51 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 231 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 51
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 231 3 6 17 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 231
  (Polychromatic418967fa.accept_22_17_7_11_1_7377 17 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 231 (Polychromatic418967fa.accept_14_2_9_7_1_5633 16 51 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 231 3 5 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 231 (Polychromatic418967fa.accept_24_14_3_15_1_13771 14 51
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 231
  (Polychromatic418967fa.accept_25_13_1_6_1_13770 13 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 231 3 4 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 231 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 51 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 231 (Polychromatic418967fa.accept_16_10_3_7_1_8094 10 51
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 231 3 3 17 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 231
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 231 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 51 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 231 3 2 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 231 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 51 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 51 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 231 3 1 17 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 231 (Polychromatic418967fa.accept_13_2_12_10_1_2649 2 51 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 231 (Polychromatic418967fa.accept_22_1_7_11_1_10772 1 51 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  231))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 231 (allA_succ_of_accept 49 50 231 (accept_3_4 49
  50 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 231
  (Polychromatic418967fa.accept_9_3_5_6_1_253 48 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 50 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 231 (accept_3_4 46 50 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 231 (Polychromatic418967fa.accept_9_8_5_6_1_538 44
  50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 231 (accept_3_4 43 50
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 231
  (Polychromatic418967fa.accept_12_6_2_3_1_354 42 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 231 (accept_3_4 40 50 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 38
  50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 231 (accept_3_4 37 50
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 231
  (Polychromatic418967fa.accept_19_17_12_3_1_12555 36 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 231 (accept_3_4 34 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 231
  (Polychromatic418967fa.accept_19_13_12_3_1_5540 32 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 231 (accept_3_4 31 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 231 (accept_3_4 28 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 50 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 231 (accept_3_4 25 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 231 (Polychromatic418967fa.accept_17_7_16_10_1_1849 24 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 231 (accept_3_4 22 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 231 (accept_3_4 19 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 231 (accept_3_4 16 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 231 (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 50 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 231
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 231 (accept_3_4 13 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 231 (accept_3_4 10 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 231 (accept_3_4 7 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 231 (accept_3_4 4 50 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 50 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  50 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 231 (accept_3_4 1 50 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 231)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 231 (allA_succ_of_accept 48 49 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 231 (accept_3_5 47 49 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 231 (accept_3_5 44 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 49 231 7 6 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 49 231 (accept_3_5 41 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 49 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 49 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 231 (accept_3_5 38 49 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 37
  49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 231
  (Polychromatic418967fa.accept_17_2_15_10_1_5171 36 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 49 231 7 5 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 49 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 49 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 231 (accept_3_5 32 49 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 231
  (Polychromatic418967fa.accept_19_12_11_3_1_8399 31 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 49 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 231 (accept_3_5 29 49 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 49 231 7 4 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 49 231 (Polychromatic418967fa.accept_19_8_11_3_1_5539 27 49 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 231 (accept_3_5 26 49 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 231
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 231 (accept_3_5 23 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 49 231 7 3 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 49 231 (accept_3_5 20 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 49 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 231 (accept_3_5 17 49 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 231
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 49 231 7 2 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 49 231 (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 49 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 49 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 231 (accept_3_5 11 49 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 231
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 231 (accept_3_5 8 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 231
  7 1 7 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 49 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 231 (accept_3_5 5 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 49 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 231 (accept_3_5 2 49 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 231))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 231 (allA_succ_of_accept 47 48 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 48 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 231 3 15 16 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 48 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 231 3 14 16 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 48 231 3 13 16 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 48 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 48 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 48 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 231 3 12 16 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 48 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 231 3 11 16 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 231 3 10 16 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 48 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 231 3 9 16 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 48 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 231 3 8 16 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 48 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 48 231 3 7 16 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 48 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 48 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 48 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 231 3 6 16 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 48 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 231 3 5 16 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 48 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 231 3 4 16 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 48 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 48 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 231 3 3 16 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 231 3 2 16 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 231
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 48 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 231 3 1 16 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 48 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  231)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 231 (allA_succ_of_accept 46 47 231 (accept_3_4 46 47
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 231
  (Polychromatic418967fa.accept_12_9_11_3_1_772 45 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 231 (accept_3_4 43 47 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 231 (Polychromatic418967fa.accept_15_12_2_6_1_2127 42 47 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 231 (accept_3_4 40 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 231 (accept_3_4 37 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 47 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 231 (accept_3_4 34 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 231 (accept_3_4 31 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 47 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 231
  (Polychromatic418967fa.accept_19_10_9_3_1_7009 29 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 231 (accept_3_4 28 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 231 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 231 (accept_3_4 25 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 47 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 231 (accept_3_4 22 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 231 (accept_3_4 19 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 231 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 47 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 231 (accept_3_4 16 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 231 (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 231 (accept_3_4 13 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 231
  (Polychromatic418967fa.accept_13_11_8_10_1_676 11 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 231 (accept_3_4 10 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 231 (accept_3_4 7 47 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 47 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 231 (accept_3_4 4 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 231 (accept_3_4 1 47 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 231))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 231 (allA_succ_of_accept 45
  46 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 46 231 (accept_3_5 44 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 46 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 46 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 46 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 231 (accept_3_5 41 46 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 40
  46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 231 (accept_3_5 38 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 231 (Polychromatic418967fa.accept_16_4_14_7_1_5641 36 46 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 231 (accept_3_5 35 46 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 46 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 231 (accept_3_5 32 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 46 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 231 (accept_3_5 29 46 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 231 (Polychromatic418967fa.accept_22_6_2_11_1_13769 28 46 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 231
  (Polychromatic418967fa.accept_10_7_6_1_1_486 27 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 231 (accept_3_5 26 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 231 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 46 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 231 (accept_3_5 23 46 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 46 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 231 (accept_3_5 20 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 46 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 231 (accept_3_5 17 46 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 46 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 231
  (Polychromatic418967fa.accept_10_5_6_1_1_836 15 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 231 (accept_3_5 14 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 46 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 231 (accept_3_5 11 46 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 231 (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 46 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 231 (accept_3_5 8 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 46 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 231 (accept_3_5 5 46 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 46 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 46
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 231 (accept_3_5 2 46 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  231)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 231 (allA_succ_of_accept 44 45 231
  (Polychromatic418967fa.accept_10_4_5_1_1_497 44 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 45 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 231 3 14 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 41
  45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 231
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 40 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 231 3 13 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 45 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 231 3 12 15 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 231
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 231 3 11 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 231 (Polychromatic418967fa.accept_14_4_3_7_1_3702
  32 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 231 3 10 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 45 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 231 (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 45
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 231 3 9 15 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 45 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 231 3 8 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 231 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 45 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 231 3 7 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 231 (Polychromatic418967fa.accept_16_4_13_7_1_4522 20 45 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 45 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 231 3 6 15 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 231 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 45 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 231 3 5 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 231 3 4 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 231 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 45 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 231 3 3 15 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 231
  (Polychromatic418967fa.accept_22_8_1_11_1_13768 8 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 45 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 231 3 2 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 45 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 231
  (Polychromatic418967fa.accept_10_4_5_1_1_497 4 45 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 231 3 1 15 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 45 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  231))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 231 (allA_succ_of_accept 43 44 231 (accept_3_4 43 44
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 231
  (Polychromatic418967fa.accept_12_6_8_3_1_82 42 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 231 (accept_3_4 40 44 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 44 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 231 (accept_3_4 37 44
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 231
  (Polychromatic418967fa.accept_16_4_12_7_1_4475 36 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 231 (accept_3_4 34 44 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 44 231 11 3 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 44 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 44 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 231 (accept_3_4 31 44 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 44 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 231 (accept_3_4 28 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 231 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 44 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 231 (accept_3_4 25 44 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 231 (Polychromatic418967fa.accept_15_9_14_6_1_3004 24 44
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 231 11 2 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 44 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 231 (accept_3_4 19 44 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18
  44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 231 (accept_3_4 16 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 44 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 231 (accept_3_4 13 44 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 44 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 44 231 11 1 4 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 44 231 (accept_3_4 10 44 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 231 (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 44 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 231
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 8 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 231 (accept_3_4 7 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  231 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 44 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 231 (accept_3_4 4 44 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 44 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 44
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 231 (accept_3_4 1 44 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 231)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  231 (allA_succ_of_accept 42 43 231 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 43 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 231 (accept_3_5 41 43 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 39
  43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 231 (accept_3_5 38 43
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 231 (Polychromatic418967fa.accept_9_1_7_6_1_75
  37 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 231 (accept_3_5 35 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 43 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 231 (accept_3_5 32 43 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 43 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 231 (accept_3_5 29 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 231 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 43 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 231 (accept_3_5 26 43 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 231 (Polychromatic418967fa.accept_19_6_5_3_1_11210 25 43 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 231
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 231 (accept_3_5 23 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 43 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 231 (accept_3_5 20 43 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 43 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 231
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 231 (accept_3_5 17 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 231 (Polychromatic418967fa.accept_16_15_11_7_1_6951 15 43 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 231 (accept_3_5 14 43 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 43 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 231 (accept_3_5 11 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 43 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 231 (accept_3_5 8 43 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 231 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 43 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 231
  (Polychromatic418967fa.accept_13_6_4_10_1_660 6 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 231 (accept_3_5 5 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 43 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 231 (accept_3_5 2 43 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 231))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 231
  (allA_succ_of_accept 41 42 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 42 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 231 3 13 14 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 42 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 231 3 12 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 231 7 5 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 42 231 (Polychromatic418967fa.accept_12_10_6_3_1_786
  34 42 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 231 3 11 14 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 231
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 42 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 231 (Polychromatic418967fa.accept_22_9_20_11_1_13767 31 42 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 231 3 10 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 231 7 4 6 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 231 3 9 14 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 231
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 42 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 42 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 231 3 8 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 231 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 42 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 42 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 42 231 21 1 2 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 42 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 42 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 231 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 42 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 231 3 6 14 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 42 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 231 3 5 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 231 7 2 6 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 231 3 4 14 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 231
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 42 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 231 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 42 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 231 3 3 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 42 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 231 7 1 6 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 231 3 2 14 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 42 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 231 3 1 14 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 42 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 231)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 231 (allA_succ_of_accept 40 41 231
  (accept_3_4 40 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 231
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 231 (accept_3_4 37 41 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 231 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 41 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 231 (accept_3_4 34 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 231 (accept_3_4 31 41 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 231 (accept_3_4 28 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 231 (Polychromatic418967fa.accept_18_9_5_15_1_2246 27 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 231 (accept_3_4 25 41 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 231 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 41 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 231
  (Polychromatic418967fa.accept_22_1_19_11_1_12229 23 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 41 231 (accept_3_4 22 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 41 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 231 (accept_3_4 19 41 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 231 (accept_3_4 16 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 231 (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 231 (accept_3_4 13 41 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 41 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 231 (accept_3_4 10 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 231 (accept_3_4 7 41 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 231
  (Polychromatic418967fa.accept_13_5_2_10_1_248 5 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 231 (accept_3_4 4 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 41 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 231 (accept_3_4 1 41 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 231))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 231 (allA_succ_of_accept 39 40 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 231 (accept_3_5 38 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 231 (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 40 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 231 (accept_3_5 35 40 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 40 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 231
  (Polychromatic418967fa.accept_14_5_12_7_1_2767 33 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 231 (accept_3_5 32 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 40 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 231 (accept_3_5 29 40 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 40 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 231
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 231 (accept_3_5 26 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 231 (Polychromatic418967fa.accept_13_11_1_10_1_648 24 40 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 231 (accept_3_5 23 40 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 231 (Polychromatic418967fa.accept_13_9_1_10_1_647 22 40 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 231 (accept_3_5 20 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 40 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 231 (accept_3_5 17 40 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 40 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 231
  (Polychromatic418967fa.accept_16_15_8_7_1_3407 15 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 231 (accept_3_5 14 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 40 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 231 (accept_3_5 11 40 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 40 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 231
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 231 (accept_3_5 8 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 40 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 231 (accept_3_5 5 40 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 231 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 40 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  40 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 231 (accept_3_5 2 40 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  231)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 231 (allA_succ_of_accept 38 39 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 39 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 39 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 231 3 12 13 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  39 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 39 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 231 3 11 13 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 231 3 10 13 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 39 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 231 3 9 13 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 39 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 231 3 8 13 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 39 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 39 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 231 3 7 13 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 39 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 39 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 231 3 6 13 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 39 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 39 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 231 3 5 13 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 39 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 39 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 231 3 4 13 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 39 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 231 3 3 13 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 39 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 231 3 2 13 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 39 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 231 3 1 13 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 39 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 39 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 231))))))))))))))))))))))))))))))))))))))) (allB_succ 38 231
  (allA_succ_of_accept 37 38 231 (accept_3_4 37 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 231 (Polychromatic418967fa.accept_20_16_18_11_1_9605 36 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 231 (accept_3_4 34 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 231 (accept_3_4 31 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 231 (accept_3_4 28 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 231 (Polychromatic418967fa.accept_20_7_18_11_1_5080 27 38 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 231 (accept_3_4 25 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 231 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 231 (accept_3_4 22 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 231
  (Polychromatic418967fa.accept_13_7_12_10_1_640 20 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 231 (accept_3_4 19 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 231 (accept_3_4 16 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 231 (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 38 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 231
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 231 (accept_3_4 13 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 231 (accept_3_4 10 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 231
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 231 (accept_3_4 7 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 231 (accept_3_4 4 38 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 38 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 231 (Polychromatic418967fa.accept_13_2_12_10_1_2649
  2 38 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 231 (accept_3_4 1 38
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 231)))))))))))))))))))))))))))))))))))))) (allB_succ 37 231
  (allA_succ_of_accept 36 37 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 37 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 231 (accept_3_5 35 37 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 231 (Polychromatic418967fa.accept_12_9_1_3_1_350
  33 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 231 (accept_3_5 32
  37 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 231
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 231 (accept_3_5 29 37 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 231
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 27 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 231 (accept_3_5 26 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 231 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 37 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 231 (accept_3_5 23 37 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 231
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 231 (accept_3_5 20 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 231 (Polychromatic418967fa.accept_14_5_9_7_1_590 19 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 231 (accept_3_5 17 37 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 231
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 231 (accept_3_5 14 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 37 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 231 (accept_3_5 11 37 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 231
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 231 (accept_3_5 8 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  231 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 231 (accept_3_5 5 37 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 37
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 231 (accept_3_5 2 37 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258
  1 37 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  231))))))))))))))))))))))))))))))))))))) (allB_succ 36 231 (allA_succ_of_accept 35 36 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 231 (Polychromatic418967fa.accept_14_6_8_7_1_589 34 36 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 231 3 11 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  32 36 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 231
  (Polychromatic418967fa.accept_19_12_17_3_1_5515 31 36 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 231 3 10 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 231 (Polychromatic418967fa.accept_14_1_8_7_1_1253 29 36 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 231 (Polychromatic418967fa.accept_16_12_4_7_1_3391 28 36
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 231 3 9 12 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 231
  (Polychromatic418967fa.accept_20_6_16_11_1_2379 26 36 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 36 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 231 3 8 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 231 (Polychromatic418967fa.accept_22_1_14_11_1_13766 23 36
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 231
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 36 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 36 231 3 7 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 36 231 (Polychromatic418967fa.accept_14_6_8_7_1_589 20 36 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 36 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 231 3 6 12 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 231
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 36 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 231 (Polychromatic418967fa.accept_19_16_17_3_1_2916 16 36 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 231 3 5 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 231 (Polychromatic418967fa.accept_16_14_4_7_1_2380 14 36 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 231
  (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 36 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 231 3 4 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 231 (Polychromatic418967fa.accept_22_10_14_11_1_12225 10 36
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 231 3 3 12 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 231
  (Polychromatic418967fa.accept_16_8_4_7_1_3390 8 36 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 231 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 36 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 231 3 2 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 36 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 231
  (Polychromatic418967fa.accept_25_4_11_6_1_13765 4 36 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 36 231 3 1 12 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 36 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 36 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 231 (Polychromatic418967fa.accept_14_1_8_7_1_1253 1 36 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 231))))))))))))))))))))))))))))))))))))
  (allB_succ 35 231 (allA_succ_of_accept 34 35 231 (accept_3_4 34 35 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 35 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 231 (accept_3_4 31 35 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 30
  35 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 35 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 35 231 7 4 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 35 231 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 35 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 231 (accept_3_4 25 35 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 231 (Polychromatic418967fa.accept_10_4_5_1_1_497
  24 35 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 231
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 35 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 231 (accept_3_4 22 35 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35
  231 7 3 5 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  35 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 35 231 (accept_3_4 19 35 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 35 231 (Polychromatic418967fa.accept_15_3_5_6_1_4005 18 35 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 231 (Polychromatic418967fa.accept_19_17_16_3_1_8401 17 35
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 231 (accept_3_4 16 35 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 231 (Polychromatic418967fa.accept_16_15_3_7_1_3389
  15 35 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 35 231 7 2 5 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 231 (accept_3_4 13
  35 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 231 (accept_3_4 10 35 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 35 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 35 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 231 7 1 5 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 231
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 35 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 35 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 231 (accept_3_4 4 35 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 231 (accept_3_4 1 35 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 231))))))))))))))))))))))))))))))))))) (allB_succ 34 231
  (allA_succ_of_accept 33 34 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 231 (accept_3_5 32 34 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 34 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 30
  34 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 231 (accept_3_5 29 34
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 231 (Polychromatic418967fa.accept_9_1_7_6_1_75
  28 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 231
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 231 (accept_3_5 26 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 231 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 34 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 231 (accept_3_5 23 34 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 34 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 231 (accept_3_5 20 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 34 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 231 (accept_3_5 17 34 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 231 (Polychromatic418967fa.accept_19_16_15_3_1_8408 16 34
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 231
  (Polychromatic418967fa.accept_10_5_4_1_1_842 15 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 231 (accept_3_5 14 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 34 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 231 (accept_3_5 11 34 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 34 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 231 (accept_3_5 8 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 34 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 231 (accept_3_5 5 34 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 34 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 34
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 231 (accept_3_5 2 34 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 231))))))))))))))))))))))))))))))))))
  (allB_succ 33 231 (allA_succ_of_accept 32 33 231 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 33 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 231
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 33 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 231 3 10 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 33 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 33 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 231 3 9 11 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 33 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 231 3 8 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 231 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 33 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 33 231 11 2 3 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 33 231 3 7 11 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 231
  (Polychromatic418967fa.accept_15_5_3_6_1_2128 20 33 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 33 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 231 3 6 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 231 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 33 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 231
  (Polychromatic418967fa.accept_13_3_7_10_1_668 16 33 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 33 231 3 5 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 33 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 33 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 231 3 4 11 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 33 231 11 1 3 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 33 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 33 231 3 3 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 33 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 33 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 33 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 231 3 2 11 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 231
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 33 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 231 (Polychromatic418967fa.accept_13_4_7_10_1_1200 4 33 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 231 3 1 11 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 231
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 33 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 231))))))))))))))))))))))))))))))))) (allB_succ 32 231 (allA_succ_of_accept 31 32 231 (accept_3_4 31 32
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 32 231
  (Polychromatic418967fa.accept_9_3_5_6_1_253 30 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 32 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 231 (accept_3_4 28 32 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 32 231 (Polychromatic418967fa.accept_15_12_2_6_1_2127 27 32 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 231 (accept_3_4 25 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 231 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 231 (accept_3_4 22 32 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 231 (accept_3_4 19 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 231 (accept_3_4 16 32 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 231 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 32 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 231
  (Polychromatic418967fa.accept_22_14_10_11_1_7472 14 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 32 231 (accept_3_4 13 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 32 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 32 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 231 (accept_3_4 10 32 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 231 (Polychromatic418967fa.accept_10_9_2_1_1_840 9
  32 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 231
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 231 (accept_3_4 7 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  231 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 32 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 231 (accept_3_4 4 32 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  32 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 231 (accept_3_4 1 32 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 231)))))))))))))))))))))))))))))))) (allB_succ 31 231
  (allA_succ_of_accept 30 31 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 31 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 231 (accept_3_5 29 31 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 231
  (Polychromatic418967fa.accept_16_11_15_7_1_5654 27 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 231 (accept_3_5 26 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 231 (Polychromatic418967fa.accept_14_10_3_7_1_1975 24 31 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 231 (accept_3_5 23 31 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 231
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 231 (accept_3_5 20 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 231 (Polychromatic418967fa.accept_14_4_3_7_1_3702 18 31 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 231 (accept_3_5 17 31 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 231
  (Polychromatic418967fa.accept_13_2_5_10_1_250 15 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 231 (accept_3_5 14 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 231 (Polychromatic418967fa.accept_17_13_14_10_1_1847 13 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 31 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 231 (accept_3_5 11 31 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 231
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 231 (accept_3_5 8 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  231 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 231 (Polychromatic418967fa.accept_13_6_5_10_1_1213 6 31 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 231 (accept_3_5 5 31 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  31 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 231 (accept_3_5 2 31 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 31
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 231)))))))))))))))))))))))))))))))
  (allB_succ 30 231 (allA_succ_of_accept 29 30 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 30 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 30 231 3 9 10 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 30 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 30 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 30 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 231 3 8 10 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 30 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 30 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 30 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 30 231 3 7 10 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 30 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 30 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 30 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 30 231 3 6 10 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 30 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 30 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 231 3 5 10 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 30 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 231 3 4 10 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 30 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 30 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 30 231 3 3 10 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 30 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 30 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 30 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 231 3 2 10 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 30 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 30 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 30 231 3 1 10 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 30 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 30 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 30 231)))))))))))))))))))))))))))))) (allB_succ 29 231 (allA_succ_of_accept 28 29 231 (accept_3_4 28 29 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 231 (Polychromatic418967fa.accept_14_13_1_7_1_1211
  27 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 231 (accept_3_4 25 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 231 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 29 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 231 (accept_3_4 22 29 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 231 (accept_3_4 19 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 29 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 231 (accept_3_4 16 29 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 29 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 231 (accept_3_4 13 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 231 (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 29 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 231 (accept_3_4 10 29 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 29 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 231 (accept_3_4 7 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 29 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 231 (accept_3_4 4 29 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 29 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 231 (accept_3_4 1 29 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 231))))))))))))))))))))))))))))) (allB_succ 28 231
  (allA_succ_of_accept 27 28 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 28 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 231 (accept_3_5 26 28 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 231
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 28 231 (accept_3_5 23 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  28 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 28 231 7 3 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 28 231 (accept_3_5 20 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 28 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 231 (accept_3_5 17 28 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 16
  28 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 231
  (Polychromatic418967fa.accept_19_15_9_3_1_13764 15 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 28 231 7 2 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 28 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 28 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 231 (accept_3_5 11 28 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 231 (Polychromatic418967fa.accept_19_10_9_3_1_7009
  10 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 231
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 231 (accept_3_5 8 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 28 231
  7 1 4 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 28 231
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 231 (accept_3_5 5 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  231 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 28 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 28 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 231 (accept_3_5 2 28 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 28 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 231)))))))))))))))))))))))))))) (allB_succ 27 231
  (allA_succ_of_accept 26 27 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 27 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 231 (Polychromatic418967fa.accept_15_10_12_6_1_3000 25 27
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 231 3 8 9 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 231
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 27 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 231 (Polychromatic418967fa.accept_13_9_1_10_1_647 22 27 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 231 3 7 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 27 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 231
  (Polychromatic418967fa.accept_16_3_11_7_1_770 19 27 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 231 3 6 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 231 (Polychromatic418967fa.accept_13_4_1_10_1_693 17 27 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 231 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 27 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 231 3 5 9 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 231
  (Polychromatic418967fa.accept_10_4_7_1_1_471 14 27 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 231 (Polychromatic418967fa.accept_19_13_8_3_1_2906 13 27 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 231 3 4 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 231 (Polychromatic418967fa.accept_13_11_1_10_1_648 11 27 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 231
  (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 27 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 231 3 3 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 231 (Polychromatic418967fa.accept_14_8_13_7_1_2798 8 27 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 231 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 27 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 231 3 2 9 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 231
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 27 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 231 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 27 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 231 3 1 9 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 231 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 27 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 231
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 27 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 231))))))))))))))))))))))))))) (allB_succ 26 231 (allA_succ_of_accept 25 26 231 (accept_3_4 25 26 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 231 (Polychromatic418967fa.accept_15_9_11_6_1_637
  24 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 26 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 26 231 (accept_3_4 22 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  26 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 26 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 26 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 231 (accept_3_4 19 26 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 26 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 26 231 (accept_3_4 16 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  26 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 26 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 26 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 231 (accept_3_4 13 26 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 26 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 231 (accept_3_4 10 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 231 (Polychromatic418967fa.accept_24_8_2_15_1_6933 8 26 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 231 (accept_3_4 7 26 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 231 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 26 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 231 (accept_3_4 4 26 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 26
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 231
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 231 (accept_3_4 1 26 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  231)))))))))))))))))))))))))) (allB_succ 25 231 (allA_succ_of_accept 24 25 231
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 231 (accept_3_5 23 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 231 (accept_3_5 20 25 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 25 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 231 (accept_3_5 17 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 231 (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 25 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 231 (accept_3_5 14 25 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 25 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 231
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 231 (accept_3_5 11 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 231 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 25 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 231 (accept_3_5 8 25 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 231 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 25 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 231 (accept_3_5 5 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 25 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 231 (accept_3_5 2 25 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 25 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 231))))))))))))))))))))))))) (allB_succ 24 231
  (allA_succ_of_accept 23 24 231 (Polychromatic418967fa.accept_18_5_6_15_1_3413 23 24 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 231 (Polychromatic418967fa.accept_18_4_6_15_1_2250 22 24
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 231 3 7 8 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 231
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 20 24 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 231 (Polychromatic418967fa.accept_15_4_9_6_1_627 19 24 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 231 3 6 8 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 231 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 24 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 231
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 24 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 231 3 5 8 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 24 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 231 (Polychromatic418967fa.accept_20_13_4_11_1_9651 13 24
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 231 3 4 8 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 231
  (Polychromatic418967fa.accept_14_11_10_7_1_1948 11 24 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 231 (Polychromatic418967fa.accept_18_10_6_15_1_3412 10 24 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 231 3 3 8 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 231 (Polychromatic418967fa.accept_13_8_11_10_1_636 8 24 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 231
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 24 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 231 3 2 8 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 231 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 24 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 231 (Polychromatic418967fa.accept_13_4_11_10_1_1226 4 24 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 231 3 1 8 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 231
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 2 24 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 231 (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 24 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 231)))))))))))))))))))))))) (allB_succ 23 231 (allA_succ_of_accept 22 23
  231 (accept_3_4 22 23 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 231
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 23 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 231 (accept_3_4 19 23 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 231 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 23 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 231 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  23 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 231 (accept_3_4 16 23
  231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 231
  (Polychromatic418967fa.accept_22_15_1_11_1_13763 15 23 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 231 (accept_3_4 13 23 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 23 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 231
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 23 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 231 (accept_3_4 10 23 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 231 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 231 (accept_3_4 7 23 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 231 (Polychromatic418967fa.accept_18_6_5_15_1_7292 6 23 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 231
  (Polychromatic418967fa.accept_14_5_9_7_1_590 5 23 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 231 (accept_3_4 4 23 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 23 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 231 (accept_3_4 1 23 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 231))))))))))))))))))))))) (allB_succ 22 231 (allA_succ_of_accept 21 22 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 231 (accept_3_5 20 22 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 231 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 22 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 231 (accept_3_5 17 22 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 22 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 231
  (Polychromatic418967fa.accept_14_1_8_7_1_1253 15 22 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 231 (accept_3_5 14 22 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 22 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 22 231 11 1 2 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 22 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 22
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 231 (accept_3_5 8 22 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 231 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 22 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 231 (accept_3_5 5 22 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 231 (Polychromatic418967fa.accept_25_4_22_6_1_13762 4 22 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  22 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 231 (accept_3_5 2 22 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 231)))))))))))))))))))))) (allB_succ 21
  231 (allA_succ_of_accept 20 21 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 231 3 6 7 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 231
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 231 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 231 3 5 7 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 21 231 7 2 3 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 231 3 4 7 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 231 3 3 7 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 231 7 1 3 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 21 231 3 2 7 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 231
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 231 3 1 7 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 231))))))))))))))))))))) (allB_succ 20 231 (allA_succ_of_accept 19 20 231 (accept_3_4 19 20 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 20 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 20 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 20 231 (accept_3_4 16 20 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  20 231 (Polychromatic418967fa.accept_14_1_6_7_1_1936 15 20 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 20 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 20 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 231 (accept_3_4 13 20 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 20 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 20 231 (accept_3_4 10 20 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  20 231 (Polychromatic418967fa.accept_17_9_3_10_1_9070 9 20 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 20 231 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 20 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 231 (accept_3_4 7 20 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 231 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 20 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 231
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 231 (accept_3_4 4 20 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  231 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 20 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 231 (Polychromatic418967fa.accept_19_2_1_3_1_11216 2 20 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 231 (accept_3_4 1 20 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 231)))))))))))))))))))) (allB_succ 19 231 (allA_succ_of_accept 18 19 231
  (Polychromatic418967fa.accept_10_8_9_1_1_189 18 19 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 231 (accept_3_5 17 19 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 19 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 231 (accept_3_5 14 19 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 231 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 19 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 231
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 231 (accept_3_5 11 19 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 231 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 231 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 19 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 231 (accept_3_5 8 19 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 231 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 231
  (Polychromatic418967fa.accept_27_6_19_15_1_13761 6 19 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 231 (accept_3_5 5 19 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 231 (accept_3_5 2 19 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 231 (Polychromatic418967fa.accept_22_1_19_11_1_12229 1 19 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 231))))))))))))))))))) (allB_succ 18 231
  (allA_succ_of_accept 17 18 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 18 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 231 3 5 6 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 231
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 18 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 18 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 231 3 4 6 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 231 (Polychromatic418967fa.accept_14_11_4_7_1_609 11 18 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 231
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 18 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 18 231 3 3 6 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 18 231 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 18 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 18 231 (Polychromatic418967fa.accept_17_7_1_10_1_2836 7 18 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 231 3 2 6 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 18 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 18 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 18 231 3 1 6 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 18 231 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 18 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 231)))))))))))))))))) (allB_succ 17 231 (allA_succ_of_accept 16 17 231 (accept_3_4 16 17 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 231 (Polychromatic418967fa.accept_19_15_17_3_1_13760 15 17
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 231 (accept_3_4 13 17 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 17 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 17 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 231 (accept_3_4 10 17 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 231 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 17 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 231 (accept_3_4 7 17 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  231 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 231 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 231 (accept_3_4 4 17 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 231 (accept_3_4 1 17 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 231))))))))))))))))) (allB_succ 16 231 (allA_succ_of_accept 15
  16 231 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 16 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 16 231 (accept_3_5 14 16 231 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 16 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 16 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 231 (accept_3_5 11 16 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 10
  16 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 231
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 16 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 231 (accept_3_5 8 16 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 231 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 16 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 231 (accept_3_5 5 16 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 231 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 16 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 16
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 231 (accept_3_5 2 16 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 231)))))))))))))))) (allB_succ 15 231
  (allA_succ_of_accept 14 15 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 15 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 231 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 15
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 231 3 4 5 77 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 231
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 15 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 231 (Polychromatic418967fa.accept_19_10_15_3_1_5470 10 15 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 231 3 3 5 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 231 (Polychromatic418967fa.accept_13_8_2_10_1_652 8 15 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 231
  (Polychromatic418967fa.accept_19_7_15_3_1_2896 7 15 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 231 3 2 5 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 231 (Polychromatic418967fa.accept_13_5_2_10_1_248 5 15 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 231 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 15 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 231 3 1 5 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 231
  (Polychromatic418967fa.accept_17_2_15_10_1_5171 2 15 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 231 (Polychromatic418967fa.accept_22_1_15_11_1_7418 1 15 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 231))))))))))))))) (allB_succ 14 231 (allA_succ_of_accept 13 14 231
  (accept_3_4 13 14 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 231
  (Polychromatic418967fa.accept_9_3_5_6_1_253 12 14 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 231 (accept_3_4 10 14 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 231 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  14 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 14 231 7 1 2 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 14 231
  (Polychromatic418967fa.accept_12_6_2_3_1_354 6 14 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 231 (accept_3_4 4 14 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 14 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 231 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  14 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 231 (accept_3_4 1 14 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 231)))))))))))))) (allB_succ 13 231 (allA_succ_of_accept 12 13
  231 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 13 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 231 (accept_3_5 11 13 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 231 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 13 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 231 (accept_3_5 8 13 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 231 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 13 231 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 231
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 231 (accept_3_5 5 13 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  231 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 231 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 13 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 231 (accept_3_5 2 13 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 231 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 13 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 231))))))))))))) (allB_succ 12 231 (allA_succ_of_accept 11 12
  231 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 12 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 12 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 231 3 3 4 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 231 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 12 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 231
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 231 3 2 4 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 231 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 231 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 12 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 231 3 1 4 77 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 231
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 12 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 231 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 12 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 231)))))))))))) (allB_succ 11 231 (allA_succ_of_accept 10 11 231
  (accept_3_4 10 11 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 231
  (Polychromatic418967fa.accept_12_9_11_3_1_772 9 11 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 231 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 231 (accept_3_4 7 11 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 231 (Polychromatic418967fa.accept_18_6_11_15_1_7255 6 11 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 231 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  11 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 231 (accept_3_4 4 11 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 231 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  11 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 231
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 231 (accept_3_4 1 11 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  231))))))))))) (allB_succ 10 231 (allA_succ_of_accept 9 10 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 231 (accept_3_5 8 10 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 231 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 231
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 10 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 231 (accept_3_5 5 10 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  231 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 10 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 231 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 10 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 231 (accept_3_5 2 10 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 231 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 231)))))))))) (allB_succ 9 231 (allA_succ_of_accept 8 9 231
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 9 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 231 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 231 3 2 3 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 231 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 9 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 231
  (Polychromatic418967fa.accept_15_4_9_6_1_627 4 9 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 231 3 1 3 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 231 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 9 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 231))))))))) (allB_succ 8 231
  (allA_succ_of_accept 7 8 231 (accept_3_4 7 8 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 231
  (Polychromatic418967fa.accept_12_6_8_3_1_82 6 8 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 231 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 231 (accept_3_4 4 8 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 231 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 8 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 231 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 8
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 231 (accept_3_4 1 8 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 231)))))))) (allB_succ 7 231 (allA_succ_of_accept 6 7 231
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 7 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 231 (accept_3_5 5 7 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 231
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 231 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 231 (accept_3_5 2 7 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 231 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 231))))))) (allB_succ 6 231 (allA_succ_of_accept 5 6 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 231 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 6 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 231 3 1 2 77 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 231 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 6 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 231
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 231)))))) (allB_succ 5 231 (allA_succ_of_accept 4 5 231 (accept_3_4 4 5 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 231 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 5 231 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 231 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5
  231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 231 (accept_3_4 1 5 231
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 231))))) (allB_succ 4 231 (allA_succ_of_accept 3 4 231
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 4 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 231 (accept_3_5 2 4 231 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 231
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 231)))) (allB_succ 3 231 (allA_succ_of_accept 2 3 231 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 3 231
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 231
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 3 231 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 231))) (allB_succ 2 231 (allA_succ_of_accept 1 2 231 (accept_3_4 1 2 231 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 231)) (allB_two
  231))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


