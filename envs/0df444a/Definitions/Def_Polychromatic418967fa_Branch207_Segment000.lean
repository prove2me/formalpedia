-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch207_Segment000
-- name    : Polychromatic418967fa_Branch207_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:30:53.020077+00:00
-- url     : https://prove2.me/theorems/7e28f0fe-ef70-4b3c-a887-3fdb9f0b6b8a
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

def Polychromatic418967fa.branch_207_segment_000 : allB 100 207 :=
  allB_succ 99 207 (allA_succ_of_accept 98 99 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 98 99 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 207
  (Polychromatic418967fa.accept_19_2_4_17_1_12087 97 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 207 3 32 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 207 (Polychromatic418967fa.accept_13_4_8_12_1_3526 95 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 94 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 207 3 31 33 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 92 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 207 (Polychromatic418967fa.accept_16_11_3_15_1_1989 91 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 207 9 10 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 89
  99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 207
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 88 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 207 3 29 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 207 (Polychromatic418967fa.accept_19_10_4_17_1_1544 86 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 85 99
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 207 3 28 33 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 207
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 83 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 207 9 9 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 80 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 207
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 79 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 207 3 26 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 207 (Polychromatic418967fa.accept_16_13_3_15_1_1931 77 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 76 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 207 3 25 33 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 207
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 74 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 207 9 8 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 207 (Polychromatic418967fa.accept_16_7_3_15_1_2940 71 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 207
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 70 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 207 3 23 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 207 (Polychromatic418967fa.accept_19_10_4_17_1_1544 67 99
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 207 3 22 33 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 207
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 65 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 207 (Polychromatic418967fa.accept_15_4_9_12_1_2495 64 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 207 9 7 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 62 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 207 3 20 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 58 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 207 3 19 33 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 207
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 56 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 207 (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 207 9 6 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 207 (Polychromatic418967fa.accept_13_1_8_12_1_2045 53 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 52 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 207 3 17 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 207 (Polychromatic418967fa.accept_15_5_9_12_1_1599 50 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 207 (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 99
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 207 3 16 33 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 46 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 207 9 5 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 207
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 43 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 207 3 14 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 207 (Polychromatic418967fa.accept_21_20_15_18_1_4457 41 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 207 3 13 33 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 207 (Polychromatic418967fa.accept_19_18_4_17_1_2618 37 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 207 9 4 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 207 (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 207
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 34 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 207 3 11 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 207 3 10 33 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 207
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 207 9 3 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 207
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 207 3 8 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 207 (Polychromatic418967fa.accept_13_10_8_12_1_2032 23 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 22 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 207 3 7 33 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 207 9 2 11 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 207
  (Polychromatic418967fa.accept_21_16_15_18_1_3050 16 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 99 207 3 5 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 99 207 (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 99 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 207
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 13 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 99 207 3 4 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 99 207 (Polychromatic418967fa.accept_16_11_3_15_1_1989 11 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 207 9 1 11 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 207
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 207 3 2 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 99 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 99 207 3 1 33 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 99 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 2 99 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 207 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 99 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  207 (allA_succ_of_accept 97 98 207 (accept_3_4 97 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 96 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 95 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 207 (accept_3_4 94 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 207
  (Polychromatic418967fa.accept_16_12_2_15_1_490 92 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 207 (accept_3_4 91 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 207 (accept_3_4 88 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 207 (Polychromatic418967fa.accept_22_21_10_9_1_2681 87 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 207
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 86 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 207 (accept_3_4 85 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 207 (Polychromatic418967fa.accept_13_6_7_12_1_3504 84 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 207 (accept_3_4 82 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 207
  (Polychromatic418967fa.accept_15_5_8_12_1_2435 80 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 207 (accept_3_4 79 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 78 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 207 (accept_3_4 76 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 75 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 74 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 207 (accept_3_4 73 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 207 (Polychromatic418967fa.accept_17_4_13_3_1_7166 72 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 207 (accept_3_4 70 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 207
  (Polychromatic418967fa.accept_21_5_14_18_1_4418 68 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 207 (accept_3_4 67 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 207 (accept_3_4 64 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 207
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 62 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 207 (accept_3_4 61 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 207 (Polychromatic418967fa.accept_13_8_7_12_1_3637 60 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 207 (accept_3_4 58 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 207
  (Polychromatic418967fa.accept_11_1_10_9_1_871 56 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 207 (accept_3_4 55 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 207 (accept_3_4 52 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 207 (Polychromatic418967fa.accept_16_3_2_15_1_7367 51 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 207
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 50 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 207 (accept_3_4 49 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 48 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 207 (accept_3_4 46 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 207
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 44 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 207 (accept_3_4 43 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 207 (accept_3_4 40 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 207
  (Polychromatic418967fa.accept_17_4_13_3_1_7166 38 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 207 (accept_3_4 37 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 207 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 207 (accept_3_4 34 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 207
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 32 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 207 (accept_3_4 31 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 207 (accept_3_4 28 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 207 (Polychromatic418967fa.accept_17_10_13_3_1_1425 27 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 207
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 207 (accept_3_4 25 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 207 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 207 (accept_3_4 22 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 207
  (Polychromatic418967fa.accept_15_5_8_12_1_2435 20 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 207 (accept_3_4 19 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 207 (accept_3_4 16 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 207
  (Polychromatic418967fa.accept_19_14_3_17_1_6558 14 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 207 (accept_3_4 13 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 207 (accept_3_4 10 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 207 (accept_3_4 7 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  207 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 207 (accept_3_4 4 98 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 98 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 207 (Polychromatic418967fa.accept_19_2_3_17_1_5146
  2 98 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 207 (accept_3_4 1 98
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  207 (allA_succ_of_accept 96 97 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 97 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 207 (accept_3_5 95 97 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 93
  97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 207 (accept_3_5 92 97
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 207
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 91 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 97 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 207 (accept_3_5 89 97 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 97 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 87
  97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 207 (accept_3_5 86 97
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 207
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 85 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 97 207 (Polychromatic418967fa.accept_20_4_17_7_1_3393 84 97 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 207 (accept_3_5 83 97 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 97 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 207 (Polychromatic418967fa.accept_12_9_1_3_1_350
  81 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 207 (accept_3_5 80
  97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 79 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 97 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 207 (accept_3_5 77 97 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 97 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 75
  97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 207 (accept_3_5 74 97
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 207 (Polychromatic418967fa.accept_7_3_6_4_1_30
  73 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 207 (accept_3_5 71 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 207 (accept_3_5 68 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 207 (Polychromatic418967fa.accept_13_2_6_12_1_1334 67 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 207 (accept_3_5 65 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 207 (Polychromatic418967fa.accept_15_3_7_12_1_372 63 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 207 (accept_3_5 62 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 207
  (Polychromatic418967fa.accept_18_6_7_9_1_4250 60 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 207 (accept_3_5 59 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 207 (accept_3_5 56 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 207 (Polychromatic418967fa.accept_15_10_7_12_1_2490 55 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 207 (accept_3_5 53 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 207 (accept_3_5 50 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 207 (Polychromatic418967fa.accept_13_10_6_12_1_2780 49 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 207
  (Polychromatic418967fa.accept_15_3_7_12_1_372 48 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 207 (accept_3_5 47 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 207 (accept_3_5 44 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 207 (Polychromatic418967fa.accept_16_11_1_15_1_1123 43 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 207 (accept_3_5 41 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 207 (Polychromatic418967fa.accept_18_3_7_9_1_5486 39 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 207 (accept_3_5 38 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 207
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 207 (accept_3_5 35 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 207 (accept_3_5 32 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 207 (accept_3_5 29 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 207 (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 207 (accept_3_5 26 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 207 (Polychromatic418967fa.accept_15_10_7_12_1_2490 25 97
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 207 (accept_3_5 23 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 207 (accept_3_5 20 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 207 (accept_3_5 17 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 207 (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 207 (accept_3_5 14 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 207 (Polychromatic418967fa.accept_27_13_16_18_1_6144 13 97
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 207 (accept_3_5 11 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 207 (accept_3_5 8 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 207 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 97 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 207 (accept_3_5 5 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 97 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 207 (accept_3_5 2 97 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 207 (Polychromatic418967fa.accept_25_1_22_7_1_12086 1 97 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 207
  (allA_succ_of_accept 95 96 207 (Polychromatic418967fa.accept_13_4_5_12_1_751 95 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 207 (Polychromatic418967fa.accept_17_9_11_3_1_2353 94 96
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 96 207 3 31 32 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 96 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 92 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 96 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 91 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 207 3 30 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 207 (Polychromatic418967fa.accept_20_9_16_7_1_1129
  89 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 96 207
  (Polychromatic418967fa.accept_21_4_12_18_1_7522 88 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 96 207 3 29 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 96 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 86 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 207 3 28 32 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 207 (Polychromatic418967fa.accept_13_4_5_12_1_751 82 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 207 3 27 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043
  80 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 79 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 207 3 26 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 96 207 (Polychromatic418967fa.accept_15_2_6_12_1_1613 77 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 96 207 3 25 32 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 96 207
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 74 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 96 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 73 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 207 3 24 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 71
  96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 207
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 70 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 96 207 3 23 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 96 207 (Polychromatic418967fa.accept_18_14_6_9_1_1950 68 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 67 96
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 207 3 22 32 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 207 3 21 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 62
  96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 207
  (Polychromatic418967fa.accept_10_1_6_7_1_710 61 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 207 3 20 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 207 (Polychromatic418967fa.accept_13_7_5_12_1_1305 59 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 96 207 3 19 32 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 96 207
  (Polychromatic418967fa.accept_13_4_5_12_1_751 56 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 96 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 207 3 18 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188
  53 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 207
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 52 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 96 207 3 17 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 96 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 207 (Polychromatic418967fa.accept_18_13_6_9_1_4280 49 96
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 207 3 16 32 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 207
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 47 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 207 (Polychromatic418967fa.accept_13_7_5_12_1_1305 46 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 207 3 15 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 44
  96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 207 3 14 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 207 (Polychromatic418967fa.accept_13_1_5_12_1_306 40 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 207 3 13 32 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 207
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 38 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 207 3 12 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 207 (Polychromatic418967fa.accept_15_5_6_12_1_916
  35 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 34 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 96 207 3 11 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 96 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 32 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 31 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 207 3 10 32 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 207 3 9 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 207 (Polychromatic418967fa.accept_17_9_11_3_1_2353 26 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 207
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 207 3 8 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 207 3 7 32 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 207 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 207 3 6 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 207 (Polychromatic418967fa.accept_13_4_5_12_1_751 17 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 16 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 96 207 3 5 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 96 207 (Polychromatic418967fa.accept_13_1_5_12_1_306 14 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 207 3 4 32 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 207
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 207 3 3 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 207
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 207 3 2 32 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 207 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 207 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 96 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 207 3 1 32 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 96 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 207
  (allA_succ_of_accept 94 95 207 (accept_3_4 94 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 93 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 207 (accept_3_4 91 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 90 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 207
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 89 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 207 (accept_3_4 88 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 207 (Polychromatic418967fa.accept_18_15_5_9_1_5529 87 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 207 (accept_3_4 85 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 84 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 83 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 207 (accept_3_4 82 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 207 (accept_3_4 79 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 78 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 207
  (Polychromatic418967fa.accept_15_2_5_12_1_369 77 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 207 (accept_3_4 76 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 207 (Polychromatic418967fa.accept_17_7_10_3_1_1421 75 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 207 (accept_3_4 73 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 207
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 71 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 207 (accept_3_4 70 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 207 (accept_3_4 67 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 66 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 207
  (Polychromatic418967fa.accept_20_5_15_7_1_7869 65 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 207 (accept_3_4 64 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 207 (accept_3_4 61 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 207
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 59 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 207 (accept_3_4 58 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 57 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 207 (accept_3_4 55 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 54 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 207 (accept_3_4 52 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 51 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 207 (accept_3_4 49 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 207
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 207 (accept_3_4 46 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 207 (accept_3_4 43 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 207
  (Polychromatic418967fa.accept_13_2_4_12_1_745 41 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 207 (accept_3_4 40 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 207 (accept_3_4 37 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 207
  (Polychromatic418967fa.accept_11_2_7_9_1_890 35 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 207 (accept_3_4 34 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 207 (accept_3_4 31 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 207 (Polychromatic418967fa.accept_17_13_10_3_1_7136 30 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 207
  (Polychromatic418967fa.accept_13_3_4_12_1_36 29 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 207 (accept_3_4 28 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 207 (accept_3_4 25 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 207 (accept_3_4 22 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 207 (accept_3_4 19 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 207
  (Polychromatic418967fa.accept_15_2_5_12_1_369 17 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 207 (accept_3_4 16 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 207 (accept_3_4 13 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 207
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 207 (accept_3_4 10 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 207 (accept_3_4 7 95 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 95 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 207
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 207 (accept_3_4 4 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  207 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 95 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 95 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 207 (accept_3_4 1 95 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 207
  (allA_succ_of_accept 93 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 207 (accept_3_5 92 94 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 90
  94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 207 (accept_3_5 89 94
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 207
  (Polychromatic418967fa.accept_19_12_18_17_1_8075 88 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 94 207 (Polychromatic418967fa.accept_13_9_3_12_1_2025 87 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 207 (accept_3_5 86 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 207
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 84 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 94 207 (accept_3_5 83 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  94 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 82 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 94 207 (accept_3_5 80 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 94 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 94 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 94 207 (accept_3_5 77 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  94 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 94 207 (Polychromatic418967fa.accept_24_3_22_15_1_1938 75 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 207 (accept_3_5 74 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 72 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 94 207 (accept_3_5 71 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  94 207 (Polychromatic418967fa.accept_19_13_18_17_1_5141 70 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 207 (accept_3_5 68 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 94 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 94 207 (accept_3_5 65 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  94 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 94 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 207 (accept_3_5 62 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 207
  (Polychromatic418967fa.accept_22_16_6_9_1_12085 60 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 94 207 (accept_3_5 59 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  94 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 94 207 (accept_3_5 56 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 94 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 94 207 (accept_3_5 53 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  94 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 94 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 207 (accept_3_5 50 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 94 207 (accept_3_5 47 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  94 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 46 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 207 (accept_3_5 44 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 207 (accept_3_5 41 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 207 (Polychromatic418967fa.accept_17_6_9_3_1_704 40 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 207 (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 207 (accept_3_5 38 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 207 (accept_3_5 35 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 207 (accept_3_5 32 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 207 (accept_3_5 29 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 207 (Polychromatic418967fa.accept_13_2_3_12_1_735 28 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 207 (accept_3_5 26 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 207
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 24 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 207 (accept_3_5 23 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 207 (accept_3_5 20 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 207 (accept_3_5 17 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 16 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 207 (accept_3_5 14 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 207 (accept_3_5 11 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 207 (Polychromatic418967fa.accept_16_10_14_15_1_2933 10 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 207 (accept_3_5 8 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 207 (accept_3_5 5 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  207 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 94 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 94 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 207 (accept_3_5 2 94 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 207
  (allA_succ_of_accept 92 93 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 92 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 91 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 207 3 30 31 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 89 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 88 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 207 3 29 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 86
  93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 85 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 207 3 28 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 207 3 27 31 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 207
  (Polychromatic418967fa.accept_17_12_8_3_1_4646 80 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 79 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 207 3 26 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 77
  93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 76 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 207 3 25 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 73 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 207 3 24 31 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 207
  (Polychromatic418967fa.accept_12_11_9_3_1_792 71 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 207 3 23 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 68
  93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 67 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 207 3 22 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 64 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 207 3 21 31 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 207 3 20 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 207 (Polychromatic418967fa.accept_12_11_9_3_1_792
  59 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 207 3 19 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 56 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 207 3 18 31 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 53 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 52 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 207 3 17 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 207 3 16 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 207 3 15 31 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 207
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 207 3 14 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 41
  93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 40 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 207 3 13 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 207 3 12 31 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 207 3 11 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802
  32 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 207 3 10 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 207 (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 93
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 207 3 9 31 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 207 3 8 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 207 3 7 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 207 3 6 31 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 207 3 5 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 207 3 4 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 207 3 3 31 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 207
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 207 3 2 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 207
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 93 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 207 3 1 31 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 93 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 207
  (allA_succ_of_accept 91 92 207 (accept_3_4 91 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 90 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 207 (accept_3_4 88 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 207
  (Polychromatic418967fa.accept_13_8_1_12_1_762 86 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 207 (accept_3_4 85 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 84 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 207 (accept_3_4 82 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 207 (Polychromatic418967fa.accept_15_6_2_12_1_885 81 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 207 (accept_3_4 79 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 207 (accept_3_4 76 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 74 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 207 (accept_3_4 73 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 207 (Polychromatic418967fa.accept_16_8_12_15_1_2005 72 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 207 (accept_3_4 70 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 69 92 207 23 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 92 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 92 207 (accept_3_4 67 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 92 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 92 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 92 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 92 207 (accept_3_4 64 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  92 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 92 207 (Polychromatic418967fa.accept_20_2_12_7_1_4799 62 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 92 207 (accept_3_4 61 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 92 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 60 92 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 92 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 92 207 (accept_3_4 58 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  92 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 57 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 92 207 (Polychromatic418967fa.accept_16_8_12_15_1_2005 56 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 92 207 (accept_3_4 55 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 92 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 92 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 92 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 92 207 (accept_3_4 52 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  92 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 92 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 50 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 92 207 (accept_3_4 49 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 92 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 48 92
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 92 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 207 23 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 92 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 92 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 92 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 92 207 (accept_3_4 43 92 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 92 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 42
  92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 92 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 92 207 (accept_3_4 40 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  92 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 92 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 92 207 (accept_3_4 37 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 92 207 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 92 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 92 207 (accept_3_4 34 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  92 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 92 207 (Polychromatic418967fa.accept_14_4_8_11_1_794 32 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 92 207 (accept_3_4 31 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 92 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 92 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 92 207 (accept_3_4 28 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  92 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 92 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 92 207 (accept_3_4 25 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 92 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 23 92 207 23 1 4 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 92 207 (accept_3_4 22 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 21 92 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 207
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 20 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 207 (accept_3_4 19 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 207 (accept_3_4 16 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 207 (accept_3_4 13 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 207 (accept_3_4 10 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 92 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 207
  (Polychromatic418967fa.accept_13_8_1_12_1_762 8 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 207 (accept_3_4 7 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 207 (accept_3_4 4 92 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 92 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 2
  92 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 207 (accept_3_4 1 92 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 207
  (allA_succ_of_accept 90 91 207 (Polychromatic418967fa.accept_16_10_11_15_1_6302 90 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 207 (accept_3_5 89 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 207 (Polychromatic418967fa.accept_14_3_7_11_1_765
  87 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 207 (accept_3_5 86
  91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 207
  (Polychromatic418967fa.accept_25_10_16_7_1_6686 85 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 207 (accept_3_5 83 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  81 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 207 (accept_3_5 80
  91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 207
  (Polychromatic418967fa.accept_15_4_1_12_1_914 79 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 91 207 (Polychromatic418967fa.accept_18_6_1_9_1_5551 78 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 207 (accept_3_5 77 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 207 (Polychromatic418967fa.accept_18_3_1_9_1_1929
  75 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 207 (accept_3_5 74
  91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 207
  (Polychromatic418967fa.accept_14_3_7_11_1_765 73 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 91 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 207 (accept_3_5 71 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  69 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 207 (accept_3_5 68
  91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 207
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 67 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 91 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 66 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 207 (accept_3_5 65 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 207
  (Polychromatic418967fa.accept_25_13_16_7_1_10504 63 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 91 207 (accept_3_5 62 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 91 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 61 91 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 91 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 207 (accept_3_5 59 91 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 58
  91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 207 (accept_3_5 56 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 207 (Polychromatic418967fa.accept_16_7_11_15_1_2929 55 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 207 (accept_3_5 53 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 207
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 51 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 207 (accept_3_5 50 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 49 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 207 (Polychromatic418967fa.accept_17_14_6_3_1_2362 48 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 207 (accept_3_5 47 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 91 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 207 (accept_3_5 44 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 207 (Polychromatic418967fa.accept_15_13_1_12_1_1638 43 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 207 (Polychromatic418967fa.accept_16_10_11_15_1_6302 42 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 207 (accept_3_5 41 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 207
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 207 (accept_3_5 38 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 207 (Polychromatic418967fa.accept_22_15_3_9_1_9061 37 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 207 (accept_3_5 35 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 207 (accept_3_5 32 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 207 (Polychromatic418967fa.accept_20_10_11_7_1_4796 30 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 207 (accept_3_5 29 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 207
  (Polychromatic418967fa.accept_19_8_15_17_1_8060 27 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 207 (accept_3_5 26 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 207 (Polychromatic418967fa.accept_21_4_7_18_1_7561 25 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 207 (accept_3_5 23 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 207 (accept_3_5 20 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 19 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 207 (Polychromatic418967fa.accept_14_4_7_11_1_790 18 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 207 (accept_3_5 17 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 207
  (Polychromatic418967fa.accept_21_15_7_18_1_4452 15 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 207 (accept_3_5 14 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 207 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 207 (accept_3_5 11 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 207 (accept_3_5 8 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  207 (Polychromatic418967fa.accept_16_7_11_15_1_2929 7 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 207 (accept_3_5 5 91 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 207
  (Polychromatic418967fa.accept_14_3_7_11_1_765 3 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 207 (accept_3_5 2 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  207 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 91 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 207
  (allA_succ_of_accept 89 90 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 88 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 207 3 29 30 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 86 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 90 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 207 3 28 30 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 207 (Polychromatic418967fa.accept_20_3_10_7_1_7839
  83 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 82 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 90 207 9 9 10 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 90 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 207 3 26 30 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 207 3 25 30 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 74
  90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 207 9 8 10 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 207 (Polychromatic418967fa.accept_20_11_10_7_1_9280 71 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 70 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 90 207 3 23 30 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 207 (Polychromatic418967fa.accept_21_4_6_18_1_9132 67 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 207 3 22 30 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 90
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 64 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 90 207 9 7 10 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 90 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 62 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 207 3 20 30 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 90 207 3 19 30 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 90 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 56
  90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 207
  (Polychromatic418967fa.accept_20_15_10_7_1_7878 55 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 207 9 6 10 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 90 207 3 17 30 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 90 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 50 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 207 3 16 30 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 47
  90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 207 9 5 10 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 207 (Polychromatic418967fa.accept_16_11_10_15_1_6301 43 90
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 207 3 14 30 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 90 207 3 13 30 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 207 9 4 10 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 207 (Polychromatic418967fa.accept_19_16_14_17_1_3863 35 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 207 3 11 30 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 207 3 10 30 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 90 207 9 3 10 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 90 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 207 3 8 30 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 207 3 7 30 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 207 9 2 10 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 207 3 5 30 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 207 3 4 30 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 207 (Polychromatic418967fa.accept_16_11_10_15_1_6301 11 90
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 90 207 9 1 10 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 207 3 2 30 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 90 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 207 3 1 30 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 90 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 207 (allA_succ_of_accept 88 89 207 (accept_3_4 88 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 87 89 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 207 (accept_3_4 85 89 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 207 (Polychromatic418967fa.accept_15_9_14_12_1_913
  84 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 83 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 207 (accept_3_4 82 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 207 (accept_3_4 79 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 207
  (Polychromatic418967fa.accept_15_2_14_12_1_2453 77 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 207 (accept_3_4 76 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 75 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 207 (accept_3_4 73 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 89 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 207 (accept_3_4 70 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 207 (accept_3_4 67 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 65 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 207 (accept_3_4 64 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 207 (Polychromatic418967fa.accept_19_6_13_17_1_8015 63 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 207 (accept_3_4 61 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 207 (Polychromatic418967fa.accept_24_12_17_15_1_12084 60 89 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 207
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 59 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 207 (accept_3_4 58 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 207 (accept_3_4 55 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 207
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 53 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 207 (accept_3_4 52 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 207 (accept_3_4 49 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 89 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 207
  (Polychromatic418967fa.accept_15_2_14_12_1_2453 47 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 207 (accept_3_4 46 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 207 (accept_3_4 43 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 207 (accept_3_4 40 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 207 (accept_3_4 37 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 89 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 207
  (Polychromatic418967fa.accept_19_16_13_17_1_12066 35 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 89 207 (accept_3_4 34 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 89 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 89 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 207 (accept_3_4 31 89 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 207 (accept_3_4 28 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 207 (accept_3_4 25 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 89 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 207 (accept_3_4 22 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 207 (accept_3_4 19 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 207
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 207 (accept_3_4 16 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 207 (accept_3_4 13 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 89 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 207
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 89 207 (accept_3_4 10 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 89 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 89 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 207 (accept_3_4 7 89 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 207
  (Polychromatic418967fa.accept_20_5_9_7_1_10766 5 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 207 (accept_3_4 4 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  207 (Polychromatic418967fa.accept_21_3_5_18_1_7512 3 89 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 207 (accept_3_4 1 89 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 207
  (allA_succ_of_accept 87 88 207 (Polychromatic418967fa.accept_13_9_10_12_1_2048 87 88 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 207 (accept_3_5 86 88 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 207
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 84 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 88 207 (accept_3_5 83 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  88 207 (Polychromatic418967fa.accept_19_6_12_17_1_12050 82 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 88 207 (Polychromatic418967fa.accept_16_1_8_15_1_1945 81 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 207 (accept_3_5 80 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 78 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 88 207 (accept_3_5 77 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  88 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 76 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 88 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 75 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 207 (accept_3_5 74 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 207
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 207 (accept_3_5 71 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 207 (Polychromatic418967fa.accept_15_10_13_12_1_3384 70 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 69 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 207 (accept_3_5 68 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 66 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 207 (accept_3_5 65 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 207 (Polychromatic418967fa.accept_14_8_4_11_1_3035 64 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 207 (accept_3_5 62 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 207
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 60 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 207 (accept_3_5 59 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 207 (Polychromatic418967fa.accept_13_6_10_12_1_2049 58 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 207 (Polychromatic418967fa.accept_14_1_4_11_1_3036 57 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 207 (accept_3_5 56 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 54 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 207 (accept_3_5 53 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 207 (Polychromatic418967fa.accept_16_4_8_15_1_1113 52 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 207 (Polychromatic418967fa.accept_18_15_16_9_1_4299 51 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 207 (accept_3_5 50 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 207
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 207 (accept_3_5 47 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047 46 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 207 (accept_3_5 44 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 207 (accept_3_5 41 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 207 (Polychromatic418967fa.accept_15_10_13_12_1_3384 40 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 207 (accept_3_5 38 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 207
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 207 (accept_3_5 35 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 207 (Polychromatic418967fa.accept_13_8_10_12_1_1337 34 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 207 (accept_3_5 32 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 207 (accept_3_5 29 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 207 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 207 (Polychromatic418967fa.accept_21_6_4_18_1_9164 27 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 207 (accept_3_5 26 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 207
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 88 207 (accept_3_5 23 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 88 207 (Polychromatic418967fa.accept_13_9_10_12_1_2048 22 88 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 207 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 88
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 207 (accept_3_5 20 88 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 207 (accept_3_5 17 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 207 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 207 (accept_3_5 14 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 207
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 207 (accept_3_5 11 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 207 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 207 (accept_3_5 8 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 207 (accept_3_5 5 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  207 (Polychromatic418967fa.accept_16_4_8_15_1_1113 4 88 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 207 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 207 (accept_3_5 2 88 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 207
  (allA_succ_of_accept 86 87 207 (Polychromatic418967fa.accept_13_8_9_12_1_2813 86 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 87 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 207 3 28 29 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 83 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 207 (Polychromatic418967fa.accept_17_14_2_3_1_7172 82 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 207 3 27 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 207 (Polychromatic418967fa.accept_19_4_11_17_1_9505
  80 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 207
  (Polychromatic418967fa.accept_17_11_2_3_1_8468 79 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 207 3 26 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 207 (Polychromatic418967fa.accept_14_7_3_11_1_2199 77 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 87 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 207 3 25 29 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 74 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 207 (Polychromatic418967fa.accept_13_8_9_12_1_2813 73 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 207 3 24 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 71
  87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 207
  (Polychromatic418967fa.accept_16_6_7_15_1_1942 70 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 207 3 23 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 68 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 67 87 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 207 3 22 29 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 207
  (Polychromatic418967fa.accept_17_14_2_3_1_7172 65 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 207 3 21 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 62
  87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 207
  (Polychromatic418967fa.accept_19_4_11_17_1_9505 61 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 207 3 20 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 207 (Polychromatic418967fa.accept_16_11_7_15_1_1998 59 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 207 (Polychromatic418967fa.accept_18_4_15_9_1_6882 58 87
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 207 3 19 29 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 207
  (Polychromatic418967fa.accept_11_1_10_9_1_871 56 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 207 3 18 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 207 (Polychromatic418967fa.accept_18_17_15_9_1_5542
  53 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 52 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 207 3 17 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 207 (Polychromatic418967fa.accept_13_10_9_12_1_2814 49 87
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 207 3 16 29 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 207
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 47 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 207 (Polychromatic418967fa.accept_16_14_7_15_1_3947 46 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 207 3 15 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 207 (Polychromatic418967fa.accept_19_6_11_17_1_2611
  44 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 207 3 14 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 207 (Polychromatic418967fa.accept_16_8_7_15_1_6339 40 87
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 207 3 13 29 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 207
  (Polychromatic418967fa.accept_16_6_7_15_1_1942 38 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 207 (Polychromatic418967fa.accept_19_18_11_17_1_12083 37 87 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 207 3 12 29 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 207
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 207 3 11 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 207
  (Polychromatic418967fa.accept_19_13_11_17_1_5152 32 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 87 207 (Polychromatic418967fa.accept_17_14_2_3_1_7172 31 87 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 207 3 10 29 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 207 (Polychromatic418967fa.accept_17_11_2_3_1_8468 28 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 207 3 9 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 207 (Polychromatic418967fa.accept_21_5_3_18_1_7508 26 87 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 207
  (Polychromatic418967fa.accept_19_6_11_17_1_2611 25 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 207 3 8 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 87 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 207 3 7 29 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 207 3 6 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 207 (Polychromatic418967fa.accept_18_17_15_9_1_5542 17 87
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 207
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 207 3 5 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 207 (Polychromatic418967fa.accept_16_14_7_15_1_3947 14 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 87 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 207 3 4 29 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 207
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 207 (Polychromatic418967fa.accept_13_10_9_12_1_2814 10 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 207 3 3 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 87 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 207
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 207 3 2 29 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 207 (Polychromatic418967fa.accept_17_5_2_3_1_9775 5 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 207 (Polychromatic418967fa.accept_18_4_15_9_1_6882 4 87 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 207 3 1 29 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 207
  (Polychromatic418967fa.accept_21_2_3_18_1_5952 2 87 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 87 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 207
  (allA_succ_of_accept 85 86 207 (accept_3_4 85 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 207 (Polychromatic418967fa.accept_19_8_10_17_1_12082 84 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 207 (accept_3_4 82 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 207
  (Polychromatic418967fa.accept_19_4_10_17_1_5194 80 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 207 (accept_3_4 79 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 78 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 207 (accept_3_4 76 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 207
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 74 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 207 (accept_3_4 73 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 207 (accept_3_4 70 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 207 (accept_3_4 67 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 207 (accept_3_4 64 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 207 (accept_3_4 61 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 207 (Polychromatic418967fa.accept_17_9_1_3_1_4626 60 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 207 (accept_3_4 58 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 207
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 56 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 207 (accept_3_4 55 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 207 (accept_3_4 52 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 51 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 207
  (Polychromatic418967fa.accept_19_12_10_17_1_5189 50 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 86 207 (accept_3_4 49 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 86 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 86 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 86 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 86 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 207 (accept_3_4 46 86 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 207
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 44 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 207 (accept_3_4 43 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 207 (accept_3_4 40 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 207 (Polychromatic418967fa.accept_16_7_6_15_1_495 39 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 207
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 38 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 207 (accept_3_4 37 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 207 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 207 (accept_3_4 34 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 207
  (Polychromatic418967fa.accept_17_15_1_3_1_1488 32 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 207 (accept_3_4 31 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 207 (accept_3_4 28 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 207 (accept_3_4 25 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 207 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 207 (accept_3_4 22 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 207 (accept_3_4 19 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 207 (accept_3_4 16 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 207 (Polychromatic418967fa.accept_17_15_1_3_1_1488 15 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 207
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 207 (accept_3_4 13 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 207 (accept_3_4 10 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 207
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 207 (accept_3_4 7 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  207 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 207 (accept_3_4 4 86 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 86 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 207 (Polychromatic418967fa.accept_17_2_1_3_1_2357 2
  86 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 207 (accept_3_4 1 86 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 207
  (allA_succ_of_accept 84 85 207 (Polychromatic418967fa.accept_13_6_7_12_1_3504 84 85 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 207 (accept_3_5 83 85 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 207 (Polychromatic418967fa.accept_12_9_1_3_1_350
  81 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 207 (accept_3_5 80
  85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 207
  (Polychromatic418967fa.accept_24_7_13_15_1_12081 79 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 207 (accept_3_5 77 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 85 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 85 207 (accept_3_5 74 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  85 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 85 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 207 (accept_3_5 71 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 69 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 85 207 (accept_3_5 68 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  85 207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 67 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 207 (accept_3_5 65 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 85 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 85 207 (accept_3_5 62 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  85 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 85 207 (Polychromatic418967fa.accept_13_8_7_12_1_3637 60 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 207 (accept_3_5 59 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 57 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 207 (accept_3_5 56 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  85 207 (Polychromatic418967fa.accept_20_15_5_7_1_4791 55 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 207 (accept_3_5 53 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 207
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 51 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 207 (accept_3_5 50 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 207 (Polychromatic418967fa.accept_13_10_7_12_1_2782 49 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 207 (accept_3_5 47 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 85 207 (accept_3_5 44 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  85 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 207 (accept_3_5 41 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 207
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 207 (accept_3_5 38 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 207 (Polychromatic418967fa.accept_13_11_7_12_1_2758 37 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 207 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 207 (accept_3_5 35 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 207 (accept_3_5 32 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 207 (accept_3_5 29 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 207
  (Polychromatic418967fa.accept_19_8_9_17_1_5151 27 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 207 (accept_3_5 26 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 207 (Polychromatic418967fa.accept_19_6_9_17_1_5214 25 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 207 (accept_3_5 23 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 207
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 207 (accept_3_5 20 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 207 (accept_3_5 17 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 207
  (Polychromatic418967fa.accept_20_15_5_7_1_4791 15 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 207 (accept_3_5 14 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 207 (accept_3_5 11 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 207 (accept_3_5 8 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 85 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 207 (accept_3_5 5 85 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 85 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 85 207 (accept_3_5 2 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85
  207 (Polychromatic418967fa.accept_16_1_5_15_1_2918 1 85 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 85 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 84 207 (allA_succ_of_accept 83 84 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 84 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 82 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 84 207 3 27 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 84 207 (Polychromatic418967fa.accept_13_2_6_12_1_1334 80 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 84 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 79 84 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 207 3 26 28 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 207
  (Polychromatic418967fa.accept_18_5_12_9_1_6871 77 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 84 207 (Polychromatic418967fa.accept_16_12_4_15_1_5091 76 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 84 207 3 25 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 84 207 (Polychromatic418967fa.accept_15_14_9_12_1_2498
  74 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 207
  (Polychromatic418967fa.accept_10_3_4_7_1_353 73 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 84 207 3 24 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 84 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 71 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 84 207 (Polychromatic418967fa.accept_13_5_6_12_1_2750 70 84
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 207 3 23 28 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 207
  (Polychromatic418967fa.accept_11_2_7_9_1_890 68 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 84 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 207 3 22 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 207 (Polychromatic418967fa.accept_15_5_9_12_1_1599
  65 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 207
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 64 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 84 207 3 21 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 84 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 61 84 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 207 3 20 28 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 207 (Polychromatic418967fa.accept_17_7_16_3_1_4660 58 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 84 207 3 19 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 84 207 (Polychromatic418967fa.accept_16_8_4_15_1_2941
  56 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 207
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 207 3 18 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 84 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 84 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 207 3 17 28 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 207
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 50 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 84 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 207 3 16 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 207 (Polychromatic418967fa.accept_17_13_16_3_1_1431
  47 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 207
  (Polychromatic418967fa.accept_11_2_7_9_1_890 46 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 84 207 3 15 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 84 207 (Polychromatic418967fa.accept_13_5_6_12_1_2750 44 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 84 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 207 3 14 28 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 207
  (Polychromatic418967fa.accept_10_1_4_7_1_374 41 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 84 207 (Polychromatic418967fa.accept_15_10_9_12_1_2497 40 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 84 207 3 13 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 84 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  38 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 207
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 37 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 84 207 3 12 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 84 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 207 (Polychromatic418967fa.accept_15_4_9_12_1_2495 34 84
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 207 3 11 28 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 207 3 10 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 207 (Polychromatic418967fa.accept_15_14_9_12_1_2498
  29 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 207
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 28 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 84 207 3 9 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 84 207 (Polychromatic418967fa.accept_27_26_3_18_1_12080 26 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 207 (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 84
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 207 3 8 28 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 207
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 84 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 207 3 7 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 207 (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 84 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 207 3 6 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 207 (Polychromatic418967fa.accept_18_17_12_9_1_3031 17 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 84 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 207 3 5 28 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 207
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 84 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 207 3 4 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 207
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 84 207 3 3 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 84 207 (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 207 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 84 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 207 3 2 28 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 207
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 207 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 84 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 207 3 1 28 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 84 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 207
  (Polychromatic418967fa.accept_10_1_4_7_1_374 1 84 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 207
  (allA_succ_of_accept 82 83 207 (accept_3_4 82 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 207 (accept_3_4 79 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 78 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 207
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 77 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 207 (accept_3_4 76 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 207 (accept_3_4 73 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 207
  (Polychromatic418967fa.accept_13_6_5_12_1_307 71 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 207 (accept_3_4 70 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 207 (accept_3_4 67 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 207 (accept_3_4 64 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 63 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 207 (accept_3_4 61 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 207 (accept_3_4 58 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 207 (accept_3_4 55 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 207
  (Polychromatic418967fa.accept_13_1_5_12_1_306 53 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 207 (accept_3_4 52 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 207 (accept_3_4 49 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 48 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 207 (accept_3_4 46 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 207 (accept_3_4 43 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 207 (Polychromatic418967fa.accept_22_20_17_9_1_7284 42 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 207
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 41 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 207 (accept_3_4 40 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 207 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 207 (accept_3_4 37 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 207 (accept_3_4 34 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 207 (accept_3_4 31 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 207
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 29 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 207 (accept_3_4 28 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 207 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 207 (accept_3_4 25 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 207 (accept_3_4 22 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 207 (accept_3_4 19 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 207 (accept_3_4 16 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 207 (accept_3_4 13 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 207
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 207 (accept_3_4 10 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 207 (accept_3_4 7 83 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 83 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 207 (accept_3_4 4 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 83 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 207 (accept_3_4 1 83 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 207 (allA_succ_of_accept 81 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 207 (accept_3_5 80 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 82 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 82 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 78 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 82 207 (accept_3_5 77 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  82 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 82 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 75 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 207 (accept_3_5 74 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 72 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 82 207 (accept_3_5 71 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  82 207 (Polychromatic418967fa.accept_13_5_4_12_1_2058 70 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 207 (accept_3_5 68 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 82 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 82 207 (accept_3_5 65 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  82 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 82 207 (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 207 (accept_3_5 62 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 207
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 207 (accept_3_5 59 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 207 (accept_3_5 56 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 207 (accept_3_5 53 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 207 (Polychromatic418967fa.accept_20_12_2_7_1_4788 52 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 207 (accept_3_5 50 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 207 (accept_3_5 47 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 46 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 207 (accept_3_5 44 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 207 (accept_3_5 41 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 207 (accept_3_5 38 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 207 (accept_3_5 35 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 207 (accept_3_5 32 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 207 (accept_3_5 29 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 28 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 207 (accept_3_5 26 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 207 (accept_3_5 23 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 207 (accept_3_5 20 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 207
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 207 (accept_3_5 17 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 207 (accept_3_5 14 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 207
  (Polychromatic418967fa.accept_16_12_2_15_1_490 12 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 207 (accept_3_5 11 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 207 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 207 (accept_3_5 8 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 82 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 207 (accept_3_5 5 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 82 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 207 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 82 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 207 (accept_3_5 2 82 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 207
  (allA_succ_of_accept 80 81 207 (Polychromatic418967fa.accept_13_2_3_12_1_735 80 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 79 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 207 3 26 27 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 77 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 76 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 207 3 25 27 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 73 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 207 9 8 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 71 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 207 3 23 27 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 207
  (Polychromatic418967fa.accept_11_2_4_9_1_484 68 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 207 3 22 27 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 65
  81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 207
  (Polychromatic418967fa.accept_10_4_1_7_1_371 64 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 207 9 7 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 207 3 20 27 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 207
  (Polychromatic418967fa.accept_12_11_9_3_1_792 59 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 207 3 19 27 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 56
  81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 207 9 6 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 207 (Polychromatic418967fa.accept_15_7_6_12_1_1614 52 81
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 207 3 17 27 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 207 3 16 27 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 207 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 207 9 5 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 44 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 207 3 14 27 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 207 (Polychromatic418967fa.accept_15_10_6_12_1_1645 40 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 207 3 13 27 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 207 9 4 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 207 3 11 27 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 207
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 32 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 207 3 10 27 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 29
  81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 207
  (Polychromatic418967fa.accept_13_2_3_12_1_735 28 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 207 9 3 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 207 3 8 27 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 207
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 207 3 7 27 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 207 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 207 9 2 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 207 3 5 27 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 207 3 4 27 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 207 9 1 9 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 207 (Polychromatic418967fa.accept_16_8_1_15_1_1982 8 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 207 3 2 27 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 81 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 207 3 1 27 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 81 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 207
  (allA_succ_of_accept 79 80 207 (accept_3_4 79 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 207 (accept_3_4 76 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 75 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 207
  (Polychromatic418967fa.accept_24_2_8_15_1_10536 74 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 207 (accept_3_4 73 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 207 (accept_3_4 70 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 207
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 68 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 207 (accept_3_4 67 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 207 (accept_3_4 64 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 207 (Polychromatic418967fa.accept_14_7_10_11_1_8112 63 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 207 (accept_3_4 61 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 207 (Polychromatic418967fa.accept_18_6_8_9_1_1960 60 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 207 (accept_3_4 58 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 207
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 56 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 207 (accept_3_4 55 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 207 (accept_3_4 52 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 51 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 207 (accept_3_4 49 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 207 (accept_3_4 46 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 207
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 44 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 207 (accept_3_4 43 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 207 (accept_3_4 40 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 207
  (Polychromatic418967fa.accept_15_8_5_12_1_4453 38 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 207 (accept_3_4 37 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 207 (accept_3_4 34 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 207 (Polychromatic418967fa.accept_22_11_14_9_1_12079 33 80 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 207
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 32 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 207 (accept_3_4 31 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 207 (accept_3_4 28 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 207
  (Polychromatic418967fa.accept_24_2_8_15_1_10536 26 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 207 (accept_3_4 25 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 24 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 207 (accept_3_4 22 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 207 (Polychromatic418967fa.accept_14_7_10_11_1_8112 21 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 207 (accept_3_4 19 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 207 (accept_3_4 16 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 207
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 14 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 207 (accept_3_4 13 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 207 (Polychromatic418967fa.accept_25_12_5_7_1_12078 12 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 207 (accept_3_4 10 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 80 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 207 (accept_3_4 7 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  207 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 207 (accept_3_4 4 80 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 207 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 80 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 207 (Polychromatic418967fa.accept_15_2_5_12_1_369 2
  80 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 207 (accept_3_4 1 80 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 207
  (allA_succ_of_accept 78 79 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 78 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 207 (accept_3_5 77 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 75
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 207 (accept_3_5 74 79
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 73 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 207 (accept_3_5 71 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 69
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 207 (accept_3_5 68 79
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 207
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 67 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 79 207 (Polychromatic418967fa.accept_20_6_19_7_1_3375 66 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 207 (accept_3_5 65 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 207 (Polychromatic418967fa.accept_13_11_1_12_1_742
  63 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 207 (accept_3_5 62
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 79 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 60 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 207 (accept_3_5 59 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  57 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 207 (accept_3_5 56
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 79 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 207 (accept_3_5 53 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 207 (Polychromatic418967fa.accept_11_7_2_9_1_480
  51 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 207 (accept_3_5 50
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 207
  (Polychromatic418967fa.accept_25_24_4_7_1_12077 49 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 79 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 207 (accept_3_5 47 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  45 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 207 (accept_3_5 44
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 207
  (Polychromatic418967fa.accept_17_9_11_3_1_2353 43 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 79 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 207 (accept_3_5 41 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 207 (Polychromatic418967fa.accept_15_9_4_12_1_1611
  39 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 207 (accept_3_5 38
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 207
  (Polychromatic418967fa.accept_11_4_2_9_1_496 37 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 79 207 (Polychromatic418967fa.accept_17_2_11_3_1_4654 36 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 207 (accept_3_5 35 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 207 (accept_3_5 32 79
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 207
  (Polychromatic418967fa.accept_13_5_1_12_1_740 31 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 79 207 (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 207 (accept_3_5 29 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 207 (accept_3_5 26 79
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 207
  (Polychromatic418967fa.accept_19_6_3_17_1_9472 25 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 79 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 207 (accept_3_5 23 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  21 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 207 (accept_3_5 20
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 79 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 207 (accept_3_5 17 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 207 (Polychromatic418967fa.accept_11_4_2_9_1_496
  15 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 207 (accept_3_5 14
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 79 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 207 (accept_3_5 11 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 79 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 207 (accept_3_5 8 79 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 7
  79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 207 (accept_3_5 5 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 207 (Polychromatic418967fa.accept_18_3_7_9_1_5486 3 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 207 (accept_3_5 2 79 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 1 79 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 207
  (allA_succ_of_accept 77 78 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 76 78
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 207 3 25 26 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 74 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 207 3 24 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 207 (Polychromatic418967fa.accept_16_7_14_15_1_2932
  71 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 70 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 207 3 23 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 67 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 207 3 22 26 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 64 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 207 3 21 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 62
  78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 207 3 20 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 207 3 19 26 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 55 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 207 3 18 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 52 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 207 3 17 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 207 3 16 26 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 207 3 15 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 44
  78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 207
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 207 3 14 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 207 3 13 26 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 207 3 12 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  35 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 207 3 11 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 207 3 10 26 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 207 3 9 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 207 3 8 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 207 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 207 3 7 26 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 207 3 6 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 207 3 5 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 207 3 4 26 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 207
  (Polychromatic418967fa.accept_17_11_10_3_1_2364 11 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 207 3 3 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 207
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 207 3 2 26 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 78 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 207 3 1 26 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 78 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 207
  (allA_succ_of_accept 76 77 207 (accept_3_4 76 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 207 (Polychromatic418967fa.accept_19_18_1_17_1_12076 75 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 207 (accept_3_4 73 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 207 (Polychromatic418967fa.accept_19_15_1_17_1_670 72 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 207
  (Polychromatic418967fa.accept_19_14_1_17_1_8063 71 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 207 (accept_3_4 70 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 207 (accept_3_4 67 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 207
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 65 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 207 (accept_3_4 64 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 63 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 207 (accept_3_4 61 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 207 (Polychromatic418967fa.accept_14_4_7_11_1_790 60 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 207
  (Polychromatic418967fa.accept_14_3_7_11_1_765 59 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 207 (accept_3_4 58 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 207 (accept_3_4 55 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 207
  (Polychromatic418967fa.accept_19_15_1_17_1_670 53 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 207 (accept_3_4 52 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 207 (Polychromatic418967fa.accept_15_6_2_12_1_885 51 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 207 (accept_3_4 49 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 48 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 207
  (Polychromatic418967fa.accept_19_9_1_17_1_3879 47 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 207 (accept_3_4 46 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 207 (accept_3_4 43 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 207
  (Polychromatic418967fa.accept_19_3_1_17_1_5159 41 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 207 (accept_3_4 40 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 207 (Polychromatic418967fa.accept_20_19_17_7_1_6299 39 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 207 (accept_3_4 37 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 207 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 207
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 207 (accept_3_4 34 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 207 (accept_3_4 31 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 207
  (Polychromatic418967fa.accept_15_14_2_12_1_2472 29 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 207 (accept_3_4 28 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 207 (Polychromatic418967fa.accept_17_10_9_3_1_7144 27 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 207 (accept_3_4 25 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 207 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 207
  (Polychromatic418967fa.accept_17_6_9_3_1_704 23 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 207 (accept_3_4 22 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 207 (accept_3_4 19 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 207
  (Polychromatic418967fa.accept_14_3_7_11_1_765 17 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 207 (accept_3_4 16 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 207 (Polychromatic418967fa.accept_18_15_5_9_1_5529 15 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 207 (accept_3_4 13 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 207 (Polychromatic418967fa.accept_16_12_13_15_1_1966 12 77 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 207
  (Polychromatic418967fa.accept_17_11_9_3_1_1463 11 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 207 (accept_3_4 10 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 207 (accept_3_4 7 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 207
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 207 (accept_3_4 4 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  207 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 77 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 77 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 207 (accept_3_4 1 77 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 77 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 76 207 (allA_succ_of_accept 75 76 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 207 (accept_3_5 74 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 207 (accept_3_5 71 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 207 (Polychromatic418967fa.accept_21_7_13_18_1_10661 70 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 207 (Polychromatic418967fa.accept_13_4_11_12_1_1318 69 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 207 (accept_3_5 68 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 207 (accept_3_5 65 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 64 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 207 (accept_3_5 62 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 207
  (Polychromatic418967fa.accept_25_10_1_7_1_12075 60 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 207 (accept_3_5 59 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 207 (Polychromatic418967fa.accept_20_17_16_7_1_12074 57 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 207 (accept_3_5 56 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 207 (accept_3_5 53 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 207 (accept_3_5 50 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 207
  (Polychromatic418967fa.accept_18_12_4_9_1_5452 48 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 207 (accept_3_5 47 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 207 (Polychromatic418967fa.accept_13_7_11_12_1_2051 46 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 207 (accept_3_5 44 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 207 (accept_3_5 41 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 207 (Polychromatic418967fa.accept_17_5_8_3_1_1419 39 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 207 (accept_3_5 38 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 207
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 76 207 (accept_3_5 35 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 76 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 34 76 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 76 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 207 (accept_3_5 32 76 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 207 (accept_3_5 29 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 207 (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 207 (accept_3_5 26 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 207 (accept_3_5 23 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 207 (Polychromatic418967fa.accept_17_5_8_3_1_1419 22 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 207 (accept_3_5 20 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 207 (accept_3_5 17 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 207 (Polychromatic418967fa.accept_18_15_4_9_1_4204 15 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 207 (accept_3_5 14 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 207 (accept_3_5 11 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 207 (accept_3_5 8 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 207 (accept_3_5 5 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  207 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 76 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 207 (accept_3_5 2 76 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 207 (allA_succ_of_accept
  74 75 207 (Polychromatic418967fa.accept_13_9_10_12_1_2048 74 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 73 75 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 207 3 24 25 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 207 (Polychromatic418967fa.accept_19_13_18_17_1_5141 70 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 207 3 23 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 68
  75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 207
  (Polychromatic418967fa.accept_13_2_10_12_1_757 67 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 207 3 22 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 75 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 207 3 21 25 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 207 (Polychromatic418967fa.accept_13_9_10_12_1_2048 61 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 207 3 20 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047
  59 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 58 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 207 3 19 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 207 (Polychromatic418967fa.accept_18_2_3_9_1_1996 56 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 75 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 207 3 18 25 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 207 3 17 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 50
  75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 207
  (Polychromatic418967fa.accept_16_1_11_15_1_498 49 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 207 3 16 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 207 (Polychromatic418967fa.accept_13_8_10_12_1_1337 47 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047 46 75
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 207 3 15 25 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 207 3 14 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 41
  75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 207
  (Polychromatic418967fa.accept_21_19_12_18_1_1798 40 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 75 207 3 13 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 75 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 38 75 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 207 3 12 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 75 207 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 75 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 207 3 11 25 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 207
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 207 (Polychromatic418967fa.accept_18_13_3_9_1_4233 31 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 207 3 10 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 28 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 75 207 3 9 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 75 207 (Polychromatic418967fa.accept_16_10_11_15_1_6302 26 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 207 (Polychromatic418967fa.accept_18_7_3_9_1_1020 25 75 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 207 3 8 25 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 207 3 7 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 75 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 207
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 19 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 207 3 6 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 207 (Polychromatic418967fa.accept_16_1_11_15_1_498 17 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 75 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 207 3 5 25 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 207
  (Polychromatic418967fa.accept_18_14_3_9_1_4234 14 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 207 3 4 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 75
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 207
  (Polychromatic418967fa.accept_16_10_11_15_1_6302 10 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 75 207 3 3 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 75 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 75 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047
  7 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 207 3 2 25 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 207
  (Polychromatic418967fa.accept_19_5_18_17_1_8017 5 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 75 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 207 3 1 25 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 75 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 75 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 207
  (allA_succ_of_accept 73 74 207 (accept_3_4 73 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  74 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 74 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 207 (accept_3_4 70 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 207
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 68 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 74 207 (accept_3_4 67 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 207 (accept_3_4 64 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 74 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 62 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 207 (accept_3_4 61 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 207 (Polychromatic418967fa.accept_13_8_9_12_1_2813 60 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 207 (accept_3_4 58 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 207
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 56 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 74 207 (accept_3_4 55 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 74 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 74 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 207 (accept_3_4 52 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 207 (Polychromatic418967fa.accept_10_1_4_7_1_374
  51 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 207
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 50 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 207 (accept_3_4 49 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 207 (Polychromatic418967fa.accept_17_14_6_3_1_2362 48 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 207 (accept_3_4 46 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 207
  (Polychromatic418967fa.accept_27_17_20_18_1_12073 44 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 74 207 (accept_3_4 43 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 74 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 74 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 207 (accept_3_4 40 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 207 (Polychromatic418967fa.accept_15_9_14_12_1_913
  39 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 207
  (Polychromatic418967fa.accept_22_16_8_9_1_12072 38 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 207 (accept_3_4 37 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 207 (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 207 (accept_3_4 34 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 207 (accept_3_4 31 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 207 (accept_3_4 28 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 207 (Polychromatic418967fa.accept_16_11_10_15_1_6301 27 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 207
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 74 207 (accept_3_4 25 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 74 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 74 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 74 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 207 (accept_3_4 22 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 207
  (Polychromatic418967fa.accept_21_20_11_18_1_3037 20 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 74 207 (accept_3_4 19 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 74 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 74 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 207 (accept_3_4 16 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 207 (Polychromatic418967fa.accept_14_1_4_11_1_3036
  15 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 207
  (Polychromatic418967fa.accept_16_14_10_15_1_3969 14 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 74 207 (accept_3_4 13 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 74 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 74 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 207 (accept_3_4 10 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 207
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 8 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 207 (accept_3_4 7 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  207 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 207 (accept_3_4 4 74 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 74 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 2
  74 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 207 (accept_3_4 1 74 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 207 (allA_succ_of_accept
  72 73 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 207 (accept_3_5 71 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 73 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 207 (accept_3_5 68 73 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 207
  (Polychromatic418967fa.accept_27_13_19_18_1_10368 67 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 73 207 (accept_3_5 65 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 73 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 207
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 73 207 (accept_3_5 62 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  73 207 (Polychromatic418967fa.accept_13_9_8_12_1_2031 61 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 73 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 207 (accept_3_5 59 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 73 207 (accept_3_5 56 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  73 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 207 (accept_3_5 53 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 73 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 207
  (Polychromatic418967fa.accept_19_13_16_17_1_5140 51 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 73 207 (accept_3_5 50 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 73 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 73 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 73 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 207 (accept_3_5 47 73 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 73 207 (accept_3_5 44 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  73 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 207 (accept_3_5 41 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 207
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 39 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 207 (accept_3_5 38 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 207 (Polychromatic418967fa.accept_19_18_16_17_1_2626 37 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 207 (accept_3_5 35 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 207 (accept_3_5 32 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 207 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 207 (accept_3_5 29 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 207 (accept_3_5 26 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 207 (accept_3_5 23 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 207 (accept_3_5 20 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 207 (Polychromatic418967fa.accept_17_2_5_3_1_1416 19 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 207 (accept_3_5 17 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 207 (accept_3_5 14 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 207 (Polychromatic418967fa.accept_24_12_1_15_1_12071 12 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 207 (accept_3_5 11 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 207 (accept_3_5 8 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 73 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 207 (accept_3_5 5 73 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 73 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 207
  (Polychromatic418967fa.accept_15_3_13_12_1_348 3 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 73 207 (accept_3_5 2 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73
  207 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 73 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 73 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 207
  (allA_succ_of_accept 71 72 207 (Polychromatic418967fa.accept_13_6_7_12_1_3504 71 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 207 (Polychromatic418967fa.accept_13_5_7_12_1_2757 70 72
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 207 3 23 24 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 207 (Polychromatic418967fa.accept_17_16_4_3_1_3429 67 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 207 3 22 24 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 65
  72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 64 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 207 9 7 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 72 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 207 3 20 24 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 207
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 59 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 207 3 19 24 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 207 (Polychromatic418967fa.accept_13_4_7_12_1_2823
  56 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 207 9 6 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 207 (Polychromatic418967fa.accept_21_11_9_18_1_4429 53 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 207 (Polychromatic418967fa.accept_16_4_8_15_1_1113 52 72
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 207 3 17 24 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 207
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 50 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 207 3 16 24 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 47
  72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 207
  (Polychromatic418967fa.accept_19_8_15_17_1_8060 46 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 207 9 5 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 207 (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 72
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 207 3 14 24 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 207 3 13 24 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 207 (Polychromatic418967fa.accept_21_17_9_18_1_7521
  38 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 207
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 37 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 207 9 4 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 72 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 207 3 11 24 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 207
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 32 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 207 (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 207 3 10 24 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096
  29 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 207
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 28 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 207 9 3 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 72 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 207 3 8 24 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 207
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 207 (Polychromatic418967fa.accept_19_3_15_17_1_12070 22 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 207 3 7 24 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 72 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 207 9 2 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 207 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 207 (Polychromatic418967fa.accept_17_16_4_3_1_3429 16 72
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 207 3 5 24 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 207 3 4 24 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 207 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 72
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 207
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 207 9 1 8 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 207 (Polychromatic418967fa.accept_13_8_7_12_1_3637 8 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 207 (Polychromatic418967fa.accept_16_7_8_15_1_6327 7 72 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 207 3 2 24 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 72 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 207 3 1 24 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 207 (Polychromatic418967fa.accept_19_2_15_17_1_2614 2 72 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 207
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 1 72 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 207
  (allA_succ_of_accept 70 71 207 (accept_3_4 70 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 207 (accept_3_4 67 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 71 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 207
  (Polychromatic418967fa.accept_25_15_21_7_1_12069 65 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 71 207 (accept_3_4 64 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 71 207 (Polychromatic418967fa.accept_25_13_21_7_1_12068 63 71 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 71 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 207 (accept_3_4 61 71 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 207 (Polychromatic418967fa.accept_14_4_1_11_1_5026
  60 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 207 (accept_3_4 58 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 207 (accept_3_4 55 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 71 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 207
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 53 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 207 (accept_3_4 52 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 51 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 207 (accept_3_4 49 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 207 (Polychromatic418967fa.accept_18_12_17_9_1_5513 48 71 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 207 (accept_3_4 46 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 207 (accept_3_4 43 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 207 (Polychromatic418967fa.accept_24_18_23_15_1_12067 42 71 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 207
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 41 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 207 (accept_3_4 40 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 207 (Polychromatic418967fa.accept_19_1_14_17_1_6605 39 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 207 (accept_3_4 37 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 71 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 207
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 35 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 207 (accept_3_4 34 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 207 (accept_3_4 31 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 207 (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 71 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 207
  (Polychromatic418967fa.accept_11_7_5_9_1_884 29 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 207 (accept_3_4 28 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 207 (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 207 (accept_3_4 25 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 207
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 207 (accept_3_4 22 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 207 (accept_3_4 19 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 71 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 207 (accept_3_4 16 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 207 (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 207 (accept_3_4 13 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 207
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 207 (accept_3_4 10 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 207 (accept_3_4 7 71 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 71 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 207 (accept_3_4 4 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 71 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 207 (accept_3_4 1 71 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 207
  (allA_succ_of_accept 69 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 207 (accept_3_5 68 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 70 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  66 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 207 (accept_3_5 65
  70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 207
  (Polychromatic418967fa.accept_19_7_13_17_1_8041 64 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 70 207 (Polychromatic418967fa.accept_19_6_13_17_1_8015 63 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 207 (accept_3_5 62 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 70 207 (Polychromatic418967fa.accept_13_8_5_12_1_2755
  60 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 207 (accept_3_5 59
  70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 207
  (Polychromatic418967fa.accept_13_6_5_12_1_307 58 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 70 207 (accept_3_5 56 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 70 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 70 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  54 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 207 (accept_3_5 53
  70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 207
  (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 70 207 (Polychromatic418967fa.accept_15_6_10_12_1_2538 51 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 70 207 (accept_3_5 50 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 207 (Polychromatic418967fa.accept_17_14_2_3_1_7172
  48 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 207 (accept_3_5 47
  70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 207
  (Polychromatic418967fa.accept_11_2_4_9_1_484 46 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 207 (accept_3_5 44 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 70 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  42 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 207 (accept_3_5 41
  70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 207
  (Polychromatic418967fa.accept_13_1_5_12_1_306 40 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 70 207 (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 207 (accept_3_5 38 70 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 207
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 70 207 (accept_3_5 35 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  70 207 (Polychromatic418967fa.accept_13_8_5_12_1_2755 34 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 207 (accept_3_5 32 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 70 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 207 (accept_3_5 29 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 207 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 207 (accept_3_5 26 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 207
  (Polychromatic418967fa.accept_11_2_4_9_1_484 24 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 207 (accept_3_5 23 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 207 (accept_3_5 20 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 70 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 207 (accept_3_5 17 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 207 (Polychromatic418967fa.accept_19_16_13_17_1_12066 16 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 70 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 207 (accept_3_5 14 70 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 207
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 207 (accept_3_5 11 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 207 (Polychromatic418967fa.accept_21_10_7_18_1_12065 10 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 207 (accept_3_5 8 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 70 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 207 (accept_3_5 5 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  207 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 70 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 70 207 (Polychromatic418967fa.accept_20_3_10_7_1_7839 3 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 207 (accept_3_5 2 70 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 207 (allA_succ_of_accept 68 69
  207 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 207 3 22 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 65
  69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 207
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 64 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 69 207 3 21 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 69 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 69 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 69 207 3 20 23 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 69 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 207 3 19 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 207
  (Polychromatic418967fa.accept_19_18_12_17_1_8026 56 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 69 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 55 69 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 207 3 18 23 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 53 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 207 3 17 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 69 207 3 16 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 69 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 69 207 23 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 69 207 3 15 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 69 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 43 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 207 3 14 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 69 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 207 3 13 23 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 207 3 12 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 207 (Polychromatic418967fa.accept_12_11_9_3_1_792
  35 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 207 3 11 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 69 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 207 3 10 23 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 207 3 9 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 207 3 8 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 23 69 207 23 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 22 69 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 207 3 7 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 69 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 207 3 6 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 69 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 207 3 5 23 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 207 3 4 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 69 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 207 3 3 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 69 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 207 3 2 23 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 207 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 69 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 207 3 1 23 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 69 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 207
  (allA_succ_of_accept 67 68 207 (accept_3_4 67 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  68 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 207 (accept_3_4 64 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 63 68 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 207 (accept_3_4 61 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 207 (Polychromatic418967fa.accept_16_12_4_15_1_5091 60 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 207 (accept_3_4 58 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 68 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 207
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 56 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 207 (accept_3_4 55 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 207 (accept_3_4 52 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 68 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 207 (accept_3_4 49 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 207 (accept_3_4 46 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 68 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 207 (accept_3_4 43 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 207 (accept_3_4 40 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 68 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 207
  (Polychromatic418967fa.accept_22_16_2_9_1_12064 38 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 207 (accept_3_4 37 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 207 (accept_3_4 34 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 68 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 207
  (Polychromatic418967fa.accept_19_13_11_17_1_5152 32 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 68 207 (accept_3_4 31 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 68 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 68 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 207 (accept_3_4 28 68 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 27
  68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 207
  (Polychromatic418967fa.accept_11_4_2_9_1_496 26 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 207 (accept_3_4 25 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 207 (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 207 (accept_3_4 22 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 207 (Polychromatic418967fa.accept_16_5_4_15_1_1102 21 68 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 207 (accept_3_4 19 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 207 (accept_3_4 16 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 68 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 207
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 14 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 207 (accept_3_4 13 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 207 (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 207 (accept_3_4 10 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 68 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 207 (accept_3_4 7 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 207 (accept_3_4 4 68 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 68 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  68 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 207 (accept_3_4 1 68 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 207 (allA_succ_of_accept 66 67
  207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 66 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 67 207 (accept_3_5 65 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 207 (Polychromatic418967fa.accept_15_3_7_12_1_372 63 67 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 207 (accept_3_5 62 67 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 207
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 61 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 67 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 67 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 67 207 (accept_3_5 59 67 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 67 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 67 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  57 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 207 (accept_3_5 56
  67 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 207
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 55 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 67 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 67 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 67 207 (accept_3_5 53 67 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 67 207 (Polychromatic418967fa.accept_15_6_7_12_1_869
  51 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 207 (accept_3_5 50
  67 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 207
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 49 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 67 207 (Polychromatic418967fa.accept_15_3_7_12_1_372 48 67 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 67 207 (accept_3_5 47 67 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 67 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  45 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 207 (accept_3_5 44
  67 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 207
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 67 207 (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 67 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 207 (accept_3_5 41 67 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 207 (Polychromatic418967fa.accept_16_7_3_15_1_2940
  39 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 207 (accept_3_5 38
  67 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 207
  (Polychromatic418967fa.accept_19_18_10_17_1_5192 37 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 67 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 207 (accept_3_5 35 67 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 67 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 207 (accept_3_5 32 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 207 (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 207 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 67 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 207 (accept_3_5 29 67 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 207
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 207 (accept_3_5 26 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 207 (Polychromatic418967fa.accept_15_10_7_12_1_2490 25 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 207 (Polychromatic418967fa.accept_17_7_16_3_1_4660 24 67 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 207 (accept_3_5 23 67 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 67 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 207
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 207 (accept_3_5 20 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 207 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 67 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 207 (accept_3_5 17 67 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 207
  (Polychromatic418967fa.accept_19_15_10_17_1_3859 15 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 67 207 (accept_3_5 14 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 67 207 (Polychromatic418967fa.accept_16_13_3_15_1_1931 13 67 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 67 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 207 (accept_3_5 11 67 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10
  67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 207 (accept_3_5 8 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  207 (Polychromatic418967fa.accept_16_7_3_15_1_2940 7 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 67 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 67 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 207 (accept_3_5 5 67 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 207
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 207 (accept_3_5 2 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67
  207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 67 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 67 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 207
  (allA_succ_of_accept 65 66 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 66 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 207 3 21 22 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 66 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 207 3 20 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 207 (Polychromatic418967fa.accept_18_5_12_9_1_6871
  59 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 58 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 66 207 3 19 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 66 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 66 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 207 3 18 22 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 66 207 3 17 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 66 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 50
  66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 207 3 16 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 66 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 47 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 66 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 207 3 15 22 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 44 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 66 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 207 3 14 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 66 207 3 13 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 66 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 207 3 12 22 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 207
  (Polychromatic418967fa.accept_14_7_10_11_1_8112 35 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 207 3 11 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 32
  66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 207
  (Polychromatic418967fa.accept_10_1_6_7_1_710 31 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 207 3 10 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 66 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 207 3 9 22 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 66 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 207 3 8 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 66 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 66 207 3 7 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 66 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 207 (Polychromatic418967fa.accept_16_3_2_15_1_7367 19 66
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 207 3 6 22 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 66 207 3 5 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 66 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 66 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 207 3 4 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 66 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 207 3 3 22 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 66 207 (Polychromatic418967fa.accept_14_7_10_11_1_8112 7 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 207 3 2 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 66 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 66 207 3 1 22 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 66 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 66 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 207 (allA_succ_of_accept 64 65 207
  (accept_3_4 64 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 207 (accept_3_4 61 65 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 207 (Polychromatic418967fa.accept_19_3_8_17_1_5213 60 65 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 207
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 59 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 207 (accept_3_4 58 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 207 (accept_3_4 55 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 207 (accept_3_4 52 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 51 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 207 (accept_3_4 49 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 65 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 207 (accept_3_4 46 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 207 (accept_3_4 43 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 207 (accept_3_4 40 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 207 (accept_3_4 37 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 65 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 207
  (Polychromatic418967fa.accept_19_16_8_17_1_5148 35 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 207 (accept_3_4 34 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 207 (accept_3_4 31 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 207
  (Polychromatic418967fa.accept_19_10_8_17_1_12063 29 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 65 207 (accept_3_4 28 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 65 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 65 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 207 (accept_3_4 25 65 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640
  24 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 207 (accept_3_4 22 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 207 (accept_3_4 19 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 207
  (Polychromatic418967fa.accept_15_2_5_12_1_369 17 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 207 (accept_3_4 16 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 207 (Polychromatic418967fa.accept_17_15_14_3_1_5947 15 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 207 (accept_3_4 13 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 207
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 207 (accept_3_4 10 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 207 (accept_3_4 7 65 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 207 (accept_3_4 4 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  207 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 65 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 207 (accept_3_4 1 65 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 207
  (allA_succ_of_accept 63 64 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 64 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 207 (accept_3_5 62 64 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 207 (Polychromatic418967fa.accept_14_4_8_11_1_794
  60 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 207 (accept_3_5 59
  64 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 207
  (Polychromatic418967fa.accept_22_14_20_9_1_10610 58 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 64 207 (Polychromatic418967fa.accept_20_17_4_7_1_4808 57 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 207 (accept_3_5 56 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 64 207 (accept_3_5 53 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  64 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 64 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 207 (accept_3_5 50 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 207
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 48 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 64 207 (accept_3_5 47 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  64 207 (Polychromatic418967fa.accept_14_4_8_11_1_794 46 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 64 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 207 (accept_3_5 44 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 64 207 (accept_3_5 41 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  64 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 64 207 (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 207 (accept_3_5 38 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 207
  (Polychromatic418967fa.accept_21_15_1_18_1_3066 36 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 207 (accept_3_5 35 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 207 (Polychromatic418967fa.accept_19_15_7_17_1_5168 34 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 207 (accept_3_5 32 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 207 (accept_3_5 29 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 207 (Polychromatic418967fa.accept_19_9_7_17_1_3875 28 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 207 (Polychromatic418967fa.accept_17_10_13_3_1_1425 27 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 207 (accept_3_5 26 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 207 (accept_3_5 23 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 207 (accept_3_5 20 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 207 (accept_3_5 17 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 16 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 207 (Polychromatic418967fa.accept_18_15_10_9_1_2009 15 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 207 (accept_3_5 14 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 207 (accept_3_5 11 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 207 (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 207 (accept_3_5 8 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 207
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 207 (accept_3_5 5 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  207 (Polychromatic418967fa.accept_14_4_8_11_1_794 4 64 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 64 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 207 (accept_3_5 2 64 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 207 (allA_succ_of_accept 62 63 207
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 62 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 63 207 (Polychromatic418967fa.accept_19_4_6_17_1_12062 61 63 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 207 3 20 21 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 207
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 59 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 63 207 (Polychromatic418967fa.accept_15_13_3_12_1_1609 58 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 207 3 19 21 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 63 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197
  56 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 63 207 9 6 7 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 63 207 (Polychromatic418967fa.accept_13_1_11_12_1_1322 53 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 207 (Polychromatic418967fa.accept_14_10_7_11_1_3015 52 63
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 207 3 17 21 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 207
  (Polychromatic418967fa.accept_19_12_6_17_1_12061 50 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 63 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 49 63 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 207 3 16 21 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 207
  (Polychromatic418967fa.accept_15_2_3_12_1_891 47 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 63 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 46 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 63 207 9 5 7 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 63 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 63 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 207
  (Polychromatic418967fa.accept_11_10_8_9_1_492 43 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 63 207 3 14 21 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 207 (Polychromatic418967fa.accept_17_7_12_3_1_4693 41 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 207 (Polychromatic418967fa.accept_13_1_11_12_1_1322 40 63
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 207 3 13 21 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 207
  (Polychromatic418967fa.accept_14_10_7_11_1_3015 38 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 37 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 207 9 4 7 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 63 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 207
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 34 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 63 207 3 11 21 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 63 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 32 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 63 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 207 3 10 21 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 207
  (Polychromatic418967fa.accept_27_2_9_18_1_12060 29 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 207 (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 207 9 3 7 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 63 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 63 207 3 8 21 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 63 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 22 63 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 207 3 7 21 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 207
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 207 (Polychromatic418967fa.accept_25_19_13_7_1_12059 19 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 207 9 2 7 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 207 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 63
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 207
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 207 3 5 21 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 63 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 207 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 63
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 207 3 4 21 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 207
  (Polychromatic418967fa.accept_19_11_6_17_1_9455 11 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 63 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 207 9 1 7 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 207 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 63 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 207
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 63 207 3 2 21 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 63 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 63 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 207 3 1 21 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 207
  (Polychromatic418967fa.accept_15_2_3_12_1_891 2 63 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 207 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 63 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 63 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 62 207 (allA_succ_of_accept 61 62 207 (accept_3_4 61 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 62 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 60 62 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 62 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 62 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 207 (accept_3_4 58 62 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 62 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 207
  (Polychromatic418967fa.accept_19_18_5_17_1_6543 56 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 62 207 (accept_3_4 55 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  62 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 62 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 207 (accept_3_4 52 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 62 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 62 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 207
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 50 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 62 207 (accept_3_4 49 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 62 207 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 62 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 62 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 62 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 207 (accept_3_4 46 62 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 207 (accept_3_4 43 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 207 (accept_3_4 40 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 62 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 207 (accept_3_4 37 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 207 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 207 (accept_3_4 34 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 207
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 32 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 207 (accept_3_4 31 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 207 (accept_3_4 28 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 62 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 207 (accept_3_4 25 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 207 (accept_3_4 22 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 62 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 207
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 207 (accept_3_4 19 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 207 (accept_3_4 16 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 62 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 207 (accept_3_4 13 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 207 (accept_3_4 10 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 207
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 207 (accept_3_4 7 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  207 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 62 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 207 (accept_3_4 4 62 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 62 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 62
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 207 (accept_3_4 1 62 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 207 (allA_succ_of_accept 60 61 207
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 60 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 207 (accept_3_5 59 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 207 (accept_3_5 56 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 61 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 207 (accept_3_5 53 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 207 (accept_3_5 50 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 207 (Polychromatic418967fa.accept_13_10_9_12_1_2814 49 61 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 207 (accept_3_5 47 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 207 (accept_3_5 44 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 61 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 207 (accept_3_5 41 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 207 (Polychromatic418967fa.accept_18_3_7_9_1_5486 39 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 207 (accept_3_5 38 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 61 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 207 (accept_3_5 35 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 207 (accept_3_5 32 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 207 (Polychromatic418967fa.accept_20_11_1_7_1_9233 31 61 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 207 (accept_3_5 29 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 207 (accept_3_5 26 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 61 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 207
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 207 (accept_3_5 23 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 207 (accept_3_5 20 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 19 61 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 207 (accept_3_5 17 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 207 (accept_3_5 14 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 61 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 207
  (Polychromatic418967fa.accept_16_12_13_15_1_1966 12 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 61 207 (accept_3_5 11 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 61 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 61 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 61 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 207 (accept_3_5 8 61 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 207 (Polychromatic418967fa.accept_17_7_10_3_1_1421
  7 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 207 (accept_3_5 5 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 61 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 207 (accept_3_5 2 61 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 207 (allA_succ_of_accept 59 60 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 60 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 207
  (Polychromatic418967fa.accept_19_1_3_17_1_1502 58 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 207 3 19 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 207 (Polychromatic418967fa.accept_13_4_8_12_1_3526 56 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 207 (Polychromatic418967fa.accept_18_1_6_9_1_2001 55 60 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 207 3 18 20 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 207
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 53 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 207 (Polychromatic418967fa.accept_16_4_12_15_1_6289 52 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 207 3 17 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 207 (Polychromatic418967fa.accept_14_8_4_11_1_3035
  50 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 207
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 207 3 16 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 207 (Polychromatic418967fa.accept_22_3_16_9_1_12058 47 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 46 60
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 207 3 15 20 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 207
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 44 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 207 3 14 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 207
  (Polychromatic418967fa.accept_24_17_12_15_1_12057 41 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 60 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 40 60 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 60 207 3 13 20 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 60 207
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 38 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 60 207 (Polychromatic418967fa.accept_18_1_6_9_1_2001 37 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 207 3 12 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 35
  60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 60 207
  (Polychromatic418967fa.accept_16_2_12_15_1_2908 34 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 60 207 3 11 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 60 207 (Polychromatic418967fa.accept_18_14_6_9_1_1950 32 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 207 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 60
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 207 3 10 20 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 207
  (Polychromatic418967fa.accept_11_7_5_9_1_884 29 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 207 (Polychromatic418967fa.accept_17_11_9_3_1_1463 28 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 207 3 9 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 207 (Polychromatic418967fa.accept_18_8_6_9_1_5576 26 60 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 207
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 25 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 207 3 8 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 207 (Polychromatic418967fa.accept_13_10_8_12_1_2032 23 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 207 (Polychromatic418967fa.accept_13_9_8_12_1_2031 22 60
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 207 3 7 20 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 60 207
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 20 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 60 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 207 3 6 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 207 (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 60 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 207
  (Polychromatic418967fa.accept_19_16_3_17_1_6575 16 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 60 207 3 5 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 60 207 (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 207 (Polychromatic418967fa.accept_16_13_12_15_1_6290 13 60
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 207 3 4 20 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 60 207 (Polychromatic418967fa.accept_13_10_8_12_1_2032 10 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 207 3 3 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 207 (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 60 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 207
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 207 3 2 20 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 207 (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 207 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 60 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 207 3 1 20 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 207
  (Polychromatic418967fa.accept_16_2_12_15_1_2908 2 60 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 60 207 (Polychromatic418967fa.accept_13_1_8_12_1_2045 1 60 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 207 (allA_succ_of_accept 58 59 207 (accept_3_4 58 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 59 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 59 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 59 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 207 (accept_3_4 55 59 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 207 (Polychromatic418967fa.accept_15_9_14_12_1_913
  54 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 207
  (Polychromatic418967fa.accept_19_15_2_17_1_5163 53 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 207 (accept_3_4 52 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 207 (Polychromatic418967fa.accept_16_3_11_15_1_1963 51 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 207 (accept_3_4 49 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 207
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 47 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 207 (accept_3_4 46 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 207 (accept_3_4 43 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 59 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 207 (accept_3_4 40 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 207 (accept_3_4 37 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 207
  (Polychromatic418967fa.accept_11_2_4_9_1_484 35 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 207 (accept_3_4 34 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 207 (accept_3_4 31 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 207 (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 59 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 207 (accept_3_4 28 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 207 (accept_3_4 25 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 59 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 207
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 207 (accept_3_4 22 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 207 (accept_3_4 19 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 59 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 207
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 207 (accept_3_4 16 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 207 (accept_3_4 13 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 207
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 207 (accept_3_4 10 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 207 (accept_3_4 7 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 59 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 207
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 207 (accept_3_4 4 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  207 (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 59 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 207 (accept_3_4 1 59 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 207
  (allA_succ_of_accept 57 58 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 207 (accept_3_5 56 58 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 54
  58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 207 (accept_3_5 53 58
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 207
  (Polychromatic418967fa.accept_19_14_1_17_1_8063 52 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 207 (Polychromatic418967fa.accept_14_9_2_11_1_780 51 58 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 207 (accept_3_5 50 58 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 48
  58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 207 (accept_3_5 47 58
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 207
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 46 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 207 (accept_3_5 44 58 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  42 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 207 (accept_3_5 41
  58 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 40 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 58 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 58 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 207 (accept_3_5 38 58 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 58 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 207
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 207 (accept_3_5 35 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 207 (accept_3_5 32 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 58 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 207 (accept_3_5 29 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 207 (accept_3_5 26 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 207
  (Polychromatic418967fa.accept_21_3_16_18_1_7500 24 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 207 (accept_3_5 23 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 207 (Polychromatic418967fa.accept_19_3_1_17_1_5159 22 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 207 (accept_3_5 20 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 207 (accept_3_5 17 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 207 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 207 (accept_3_5 14 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 207 (accept_3_5 11 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 207 (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 207 (accept_3_5 8 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 207 (accept_3_5 5 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  207 (Polychromatic418967fa.accept_17_4_7_3_1_1417 4 58 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 207 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 207 (accept_3_5 2 58 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  207)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 207 (allA_succ_of_accept 56 57 207
  (Polychromatic418967fa.accept_13_4_5_12_1_751 56 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 55 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 207 3 18 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 53
  57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 52 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 207 3 17 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 57 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 207 3 16 19 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 207 3 15 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 207 (Polychromatic418967fa.accept_18_8_3_9_1_4232
  44 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 43 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 207 3 14 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 57 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 207 3 13 19 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 207 3 12 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 207 (Polychromatic418967fa.accept_12_11_9_3_1_792
  35 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 207 3 11 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 207 (Polychromatic418967fa.accept_13_6_5_12_1_307 32 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 57 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 207 3 10 19 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 29 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 207 3 9 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 207 3 8 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 207 3 7 19 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 207
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 207 3 6 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 207
  (Polychromatic418967fa.accept_20_16_17_7_1_7845 16 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 207 3 5 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 57 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 207 3 4 19 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 207
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 207 3 3 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 207 (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 57 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 7 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 207 3 2 19 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 57 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 207 3 1 19 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 57 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 207 (allA_succ_of_accept 55 56 207 (accept_3_4 55 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 56 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 207 (accept_3_4 52 56 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 207 (Polychromatic418967fa.accept_10_1_6_7_1_710
  51 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 207
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 50 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 207 (accept_3_4 49 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 207 (Polychromatic418967fa.accept_19_10_18_17_1_8030 48 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 207 (accept_3_4 46 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 207 (Polychromatic418967fa.accept_19_7_18_17_1_663 45 56 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 207
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 44 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 207 (accept_3_4 43 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 207 (accept_3_4 40 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 207 (Polychromatic418967fa.accept_16_7_8_15_1_6327 39 56 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 207
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 38 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 207 (accept_3_4 37 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 207 (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 207 (accept_3_4 34 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 56 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 207
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 207 (accept_3_4 31 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 207 (accept_3_4 28 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 207 (Polychromatic418967fa.accept_21_6_14_18_1_12056 27 56 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 207
  (Polychromatic418967fa.accept_19_7_18_17_1_663 26 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 207 (accept_3_4 25 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 207 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 207 (accept_3_4 22 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 56 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 207
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 207 (accept_3_4 19 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 207 (accept_3_4 16 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 56 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 207
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 56 207 (accept_3_4 13 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 56 207 (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 56 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 207 (accept_3_4 10 56 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 207 (Polychromatic418967fa.accept_16_9_8_15_1_5095
  9 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 207
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 207 (accept_3_4 7 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 207 (accept_3_4 4 56 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 56 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 207 (Polychromatic418967fa.accept_13_2_4_12_1_745 2
  56 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 207 (accept_3_4 1 56 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 207))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 207 (allA_succ_of_accept 54 55 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 207 (accept_3_5 53 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 207 (accept_3_5 50 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 207 (Polychromatic418967fa.accept_21_7_13_18_1_10661 49 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 207 (accept_3_5 47 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 207 (accept_3_5 44 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 207 (accept_3_5 41 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 207
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 207 (accept_3_5 38 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 207 (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 207 (accept_3_5 35 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 55 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 207 (accept_3_5 32 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 207 (accept_3_5 29 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 207
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 207 (accept_3_5 26 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 207 (Polychromatic418967fa.accept_20_5_15_7_1_7869 25 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 207 (accept_3_5 23 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 207 (accept_3_5 20 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 207 (accept_3_5 17 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 207
  (Polychromatic418967fa.accept_13_2_3_12_1_735 15 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 207 (accept_3_5 14 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 207 (accept_3_5 11 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 207 (accept_3_5 8 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 55 207 (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 207 (accept_3_5 5 55 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 55 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 55 207 (accept_3_5 2 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55
  207 (Polychromatic418967fa.accept_20_1_15_7_1_3405 1 55 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 55 207))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 207
  (allA_succ_of_accept 53 54 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 54 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 207 3 17 18 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 54 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 207 3 16 18 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 207 (Polychromatic418967fa.accept_21_5_12_18_1_7637
  47 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 54 207 9 5 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 54 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 54 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 207 3 14 18 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 54 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 207 3 13 18 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 38
  54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 207 9 4 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 207 (Polychromatic418967fa.accept_15_5_9_12_1_1599 35 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 54 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 207 3 11 18 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 54 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 207 3 10 18 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 54 207 9 3 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 54 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 207 3 8 18 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 54 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 207 3 7 18 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 54 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 207 9 2 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 54 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 207 3 5 18 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 207
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 54 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 207 3 4 18 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 54 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 54 207 9 1 6 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 54 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 207 (Polychromatic418967fa.accept_16_7_6_15_1_495 7 54 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 207 3 2 18 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 54 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 54 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 207 3 1 18 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 54 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 207)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 207 (allA_succ_of_accept 52 53
  207 (accept_3_4 52 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 207
  (Polychromatic418967fa.accept_18_15_17_9_1_4200 51 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 207 (accept_3_4 49 53 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 48 53 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 207 (Polychromatic418967fa.accept_13_8_1_12_1_762
  47 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 207 (accept_3_4 46
  53 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 207 (accept_3_4 43 53 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 207 (Polychromatic418967fa.accept_13_2_1_12_1_1326
  41 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 207 (accept_3_4 40
  53 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 207
  (Polychromatic418967fa.accept_17_5_2_3_1_9775 39 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 207 (accept_3_4 37 53 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 53 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108
  35 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 207 (accept_3_4 34
  53 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 207
  (Polychromatic418967fa.accept_12_9_5_3_1_782 33 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 53 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 207 (accept_3_4 31 53 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 53 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 207
  (Polychromatic418967fa.accept_19_10_15_17_1_6590 29 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 53 207 (accept_3_4 28 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 53 207 (Polychromatic418967fa.accept_19_8_15_17_1_8060 27 53 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 207 (accept_3_4 25 53 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110
  24 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 207
  (Polychromatic418967fa.accept_24_23_5_15_1_12055 23 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 53 207 (accept_3_4 22 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 53 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 53 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 207 (accept_3_4 19 53 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 207
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 207 (accept_3_4 16 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 207 (accept_3_4 13 53 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 207 (Polychromatic418967fa.accept_18_12_17_9_1_5513 12 53 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 207
  (Polychromatic418967fa.accept_13_11_1_12_1_742 11 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 207 (accept_3_4 10 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 207 (accept_3_4 7 53 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 207 (accept_3_4 4 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  207 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 53 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 53 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 207 (accept_3_4 1 53 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 53 207))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 207
  (allA_succ_of_accept 51 52 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 207 (accept_3_5 50 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 48
  52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 207 (accept_3_5 47 52
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 207
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 46 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 207 (accept_3_5 44 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 207 (Polychromatic418967fa.accept_12_6_4_3_1_361
  42 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 207 (accept_3_5 41
  52 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 207
  (Polychromatic418967fa.accept_15_10_7_12_1_2490 40 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 52 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 207 (accept_3_5 38 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 52 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 36
  52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 207 (accept_3_5 35 52
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 52 207 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 207 (accept_3_5 32 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 52 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 207 (Polychromatic418967fa.accept_12_6_4_3_1_361
  30 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 207 (accept_3_5 29
  52 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 207
  (Polychromatic418967fa.accept_16_12_4_15_1_5091 28 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 52 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 207 (accept_3_5 26 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 52 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 207 (Polychromatic418967fa.accept_10_4_2_7_1_373
  24 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 207 (accept_3_5 23
  52 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 52 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 207 (accept_3_5 20 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 52 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 207 (Polychromatic418967fa.accept_12_6_4_3_1_361
  18 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 207 (accept_3_5 17
  52 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 207
  (Polychromatic418967fa.accept_19_16_14_17_1_3863 16 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 207 (accept_3_5 14 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 207
  (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 207 (accept_3_5 11 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 207 (accept_3_5 8 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 207 (accept_3_5 5 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 52 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 207 (accept_3_5 2 52 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 207))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 207 (allA_succ_of_accept 50 51 207 (Polychromatic418967fa.accept_15_5_6_12_1_916 50 51 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 207
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 51 207 3 16 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 51 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 46 51 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 207 3 15 17 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 44 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 207 (Polychromatic418967fa.accept_16_11_3_15_1_1989 43 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 207 3 14 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 41
  51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 40 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 51 207 3 13 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 51 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 38 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 207 (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 51
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 207 3 12 17 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 207
  (Polychromatic418967fa.accept_11_2_7_9_1_890 35 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 207 3 11 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 207 (Polychromatic418967fa.accept_15_2_6_12_1_1613
  32 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 207
  (Polychromatic418967fa.accept_21_10_9_18_1_7628 31 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 207 3 10 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 207 (Polychromatic418967fa.accept_16_13_3_15_1_1931 29 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 51 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 207 3 9 17 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 207 (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 207 3 8 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 207 (Polychromatic418967fa.accept_16_7_3_15_1_2940 23 51 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 207
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 22 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 207 3 7 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 51 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 207 3 6 17 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 207
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 207 3 5 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 51 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 207 3 4 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 207 (Polychromatic418967fa.accept_16_11_3_15_1_1989 11 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 207 (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 51
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 207 3 3 17 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 207
  (Polychromatic418967fa.accept_21_8_9_18_1_4430 8 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 207 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 207 3 2 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 51 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 51 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 207 3 1 17 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 51 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 207 (Polychromatic418967fa.accept_20_1_11_7_1_10755 1 51 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  207))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 207 (allA_succ_of_accept 49 50 207 (accept_3_4 49
  50 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 207
  (Polychromatic418967fa.accept_19_10_12_17_1_1506 48 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 50 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 207 (accept_3_4 46 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 207
  (Polychromatic418967fa.accept_16_12_2_15_1_490 44 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 207 (accept_3_4 43 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 207 (accept_3_4 40 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 207 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 50 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 207 (accept_3_4 37 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 207 (accept_3_4 34 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 207
  (Polychromatic418967fa.accept_14_4_8_11_1_794 32 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 207 (accept_3_4 31 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 207 (accept_3_4 28 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 207 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 50 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 207 (accept_3_4 25 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 207 (accept_3_4 22 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 50 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 207
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 207 (accept_3_4 19 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 207 (accept_3_4 16 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 207 (Polychromatic418967fa.accept_19_15_12_17_1_5195 15 50 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 207
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 207 (accept_3_4 13 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 207 (accept_3_4 10 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 207
  (Polychromatic418967fa.accept_15_8_5_12_1_4453 8 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 207 (accept_3_4 7 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  207 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 207 (accept_3_4 4 50 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 50 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 207 (Polychromatic418967fa.accept_15_2_5_12_1_369 2
  50 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 207 (accept_3_4 1 50 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 207)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 207 (allA_succ_of_accept 48 49 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 207 (accept_3_5 47 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 207 (accept_3_5 44 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 207 (Polychromatic418967fa.accept_16_11_1_15_1_1123 43 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 207 (accept_3_5 41 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 207
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 207 (accept_3_5 38 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 37 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 207 (Polychromatic418967fa.accept_20_16_9_7_1_3402 36 49 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 207 (accept_3_5 35 49 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 207 (accept_3_5 32 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 31 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 207 (accept_3_5 29 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 207
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 207 (accept_3_5 26 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 207 (Polychromatic418967fa.accept_19_6_11_17_1_2611 25 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 49 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 207 (accept_3_5 23 49 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 207 (accept_3_5 20 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 207 (Polychromatic418967fa.accept_13_6_10_12_1_2049 19 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 207 (accept_3_5 17 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 207
  (Polychromatic418967fa.accept_13_2_10_12_1_757 15 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 207 (accept_3_5 14 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 207 (Polychromatic418967fa.accept_19_13_11_17_1_5152 13 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 207 (accept_3_5 11 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 207 (accept_3_5 8 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  207 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 207 (accept_3_5 5 49 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 3
  49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 207 (accept_3_5 2 49 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401
  1 49 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  207))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 207 (allA_succ_of_accept 47 48 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 207 3 15 16 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 207
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 207 3 14 16 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 207 (Polychromatic418967fa.accept_18_5_12_9_1_6871 41 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 48 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 48 207 3 13 16 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 48 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 48 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 207 3 12 16 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  35 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 207
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 34 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 48 207 3 11 16 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 48 207 (Polychromatic418967fa.accept_15_2_3_12_1_891 32 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 207 3 10 16 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 207
  (Polychromatic418967fa.accept_10_9_8_7_1_714 29 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 207 (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 207 3 9 16 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 48 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 207
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 207 3 8 16 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 22 48 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 207 3 7 16 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 207
  (Polychromatic418967fa.accept_19_1_10_17_1_5188 20 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 48 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 207 3 6 16 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 48 207 3 5 16 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 48 207 (Polychromatic418967fa.accept_21_14_6_18_1_12047 14 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 48 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 207 3 4 16 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 207
  (Polychromatic418967fa.accept_17_11_14_3_1_1427 11 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 207 3 3 16 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 207 (Polychromatic418967fa.accept_13_8_9_12_1_2813 8 48 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 207
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 207 3 2 16 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 207 (Polychromatic418967fa.accept_18_4_12_9_1_2011 4 48 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 207 3 1 16 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 48 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 48 207 (Polychromatic418967fa.accept_19_1_10_17_1_5188 1 48 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 207)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 207
  (allA_succ_of_accept 46 47 207 (accept_3_4 46 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 207 (accept_3_4 43 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 207 (Polychromatic418967fa.accept_17_8_13_3_1_3432 42 47 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 207 (accept_3_4 40 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 207 (accept_3_4 37 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 207
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 207 (accept_3_4 34 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 207 (accept_3_4 31 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 47 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 207 (accept_3_4 28 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 207 (accept_3_4 25 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 207 (Polychromatic418967fa.accept_21_3_5_18_1_7512 24 47 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 207 (accept_3_4 22 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 207 (accept_3_4 19 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 207 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 47 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 207
  (Polychromatic418967fa.accept_11_6_3_9_1_906 17 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 207 (accept_3_4 16 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 207 (accept_3_4 13 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 207 (Polychromatic418967fa.accept_18_12_11_9_1_4257 12 47 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 207
  (Polychromatic418967fa.accept_19_11_9_17_1_8038 11 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 207 (accept_3_4 10 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 207 (accept_3_4 7 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 47 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 207
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 207 (accept_3_4 4 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 47 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 207 (accept_3_4 1 47 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 207))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 207
  (allA_succ_of_accept 45 46 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 207 (accept_3_5 44 46 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 46 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 46 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  42 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 207 (accept_3_5 41
  46 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 40 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 207 (Polychromatic418967fa.accept_16_7_14_15_1_2932 39 46 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 207 (accept_3_5 38 46 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 207
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 46 207 (accept_3_5 35 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  46 207 (Polychromatic418967fa.accept_13_8_7_12_1_3637 34 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 46 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 207 (accept_3_5 32 46 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 46 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 46 207 (accept_3_5 29 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  46 207 (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 46 207 (Polychromatic418967fa.accept_21_6_4_18_1_9164 27 46 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 207 (accept_3_5 26 46 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 46 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 207
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 23 46 207 23 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 22 46 207 (Polychromatic418967fa.accept_14_8_4_11_1_3035 22 46 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 207 (accept_3_5 20 46 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 46 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 46 207 (accept_3_5 17 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  46 207 (Polychromatic418967fa.accept_19_16_8_17_1_5148 16 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 46 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 46 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 207 (accept_3_5 14 46 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 46 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 207
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 46 207 (accept_3_5 11 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  46 207 (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 46 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 207 (accept_3_5 8 46 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 46 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 46 207 (accept_3_5 5 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46
  207 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 46 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 46 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 46 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 207 (accept_3_5 2 46 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 46 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 207)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45
  207 (allA_succ_of_accept 44 45 207 (Polychromatic418967fa.accept_13_5_6_12_1_2750 44 45 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 43
  45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 207 3 14 15 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 207 (Polychromatic418967fa.accept_19_2_7_17_1_12054 40 45 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 45 207 3 13 15 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 45 207 9 4 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 45 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 45 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 207 3 11 15 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 207
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 45 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 207 3 10 15 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 29
  45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 207
  (Polychromatic418967fa.accept_10_8_5_7_1_358 28 45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 207 9 3 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 45 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 207 3 8 15 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 207 3 7 15 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 45 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 45 207 9 2 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 45 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 45 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 207 (Polychromatic418967fa.accept_19_16_7_17_1_3853 16 45
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 207 3 5 15 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 45 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 207 3 4 15 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 45 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 45 207 9 1 5 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 45 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 45 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 207 3 2 15 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 207 (Polychromatic418967fa.accept_21_4_3_18_1_7550 4 45 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 207 3 1 15 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 45 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 207))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 207 (allA_succ_of_accept 43 44 207
  (accept_3_4 43 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 207 (accept_3_4 40 44 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 44 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 207
  (Polychromatic418967fa.accept_25_13_19_7_1_6688 38 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 207 (accept_3_4 37 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 207 (Polychromatic418967fa.accept_16_4_12_15_1_6289 36 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 207 (accept_3_4 34 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 44 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 207 (accept_3_4 31 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 207 (accept_3_4 28 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 44 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 207 (accept_3_4 25 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 207 (accept_3_4 22 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 44 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 207 (accept_3_4 19 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 207 (accept_3_4 16 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 207 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 44 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 207
  (Polychromatic418967fa.accept_13_1_5_12_1_306 14 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 207 (accept_3_4 13 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 207 (accept_3_4 10 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 207 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 44 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 207
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 207 (accept_3_4 7 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  207 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 207 (accept_3_4 4 44 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 44 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 2
  44 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 207 (accept_3_4 1 44 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 207)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  207 (allA_succ_of_accept 42 43 207 (Polychromatic418967fa.accept_13_3_4_12_1_36 42 43 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 207 (accept_3_5 41 43 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 207
  (Polychromatic418967fa.accept_16_7_11_15_1_2929 39 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 207 (accept_3_5 38 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 207 (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 43 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 207 (accept_3_5 35 43 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 43 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 207 (accept_3_5 32 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 43 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 207 (accept_3_5 29 43 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 207
  (Polychromatic418967fa.accept_17_10_9_3_1_7144 27 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 207 (accept_3_5 26 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 207 (accept_3_5 23 43 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 207 (accept_3_5 20 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 207 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 43 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 207 (accept_3_5 17 43 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 207 (accept_3_5 14 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 207 (Polychromatic418967fa.accept_22_13_21_9_1_4104 13 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 207 (accept_3_5 11 43 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 207 (accept_3_5 8 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 43 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 43 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 207 (accept_3_5 5 43 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 207 (accept_3_5 2 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43
  207 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 43 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 43 207))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 207 (allA_succ_of_accept 41 42
  207 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 42 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 207 3 13 14 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 38
  42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 207 3 12 14 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 42 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 42 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 207 3 11 14 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 207 (Polychromatic418967fa.accept_18_13_6_9_1_4280 31 42 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 207 3 10 14 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 42 207 3 9 14 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 42 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 42 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 207 3 8 14 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 207
  (Polychromatic418967fa.accept_22_1_20_9_1_12053 23 42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 42 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 207 3 7 14 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 42 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 207
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 207 3 6 14 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 42 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 207 3 5 14 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 42 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 207 3 4 14 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 207 (Polychromatic418967fa.accept_16_11_10_15_1_6301 11 42
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 42 207 3 3 14 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 42 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 42 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 207 (Polychromatic418967fa.accept_18_7_6_9_1_4205 7 42 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 207 3 2 14 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 42 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 207 3 1 14 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 42 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 207)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 207 (allA_succ_of_accept 40 41 207
  (accept_3_4 40 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 207
  (Polychromatic418967fa.accept_19_1_3_17_1_1502 39 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 207 (accept_3_4 37 41 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 207
  (Polychromatic418967fa.accept_19_16_3_17_1_6575 35 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 207 (accept_3_4 34 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 207 (accept_3_4 31 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 207
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 207 (accept_3_4 28 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 207 (accept_3_4 25 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 207 (accept_3_4 22 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 207 (accept_3_4 19 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 207 (accept_3_4 16 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 207 (Polychromatic418967fa.accept_18_15_5_9_1_5529 15 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 207 (accept_3_4 13 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 207
  (Polychromatic418967fa.accept_20_11_1_7_1_9233 11 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 207 (accept_3_4 10 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 207 (accept_3_4 7 41 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 207 (accept_3_4 4 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 41 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 207 (accept_3_4 1 41 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 207))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 207 (allA_succ_of_accept 39 40 207
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 207 (accept_3_5 38 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 40 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 207 (accept_3_5 35 40 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 40 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 207
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 33 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 207 (accept_3_5 32 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 40 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 207 (accept_3_5 29 40 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 207 (Polychromatic418967fa.accept_13_2_1_12_1_1326 28 40 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 207 (accept_3_5 26 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 40 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 207 (accept_3_5 23 40 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 40 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 207
  (Polychromatic418967fa.accept_13_8_1_12_1_762 21 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 207 (accept_3_5 20 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 40 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 207 (accept_3_5 17 40 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 40 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 207 (accept_3_5 14 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 207 (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 40 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 207 (accept_3_5 11 40 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 207 (Polychromatic418967fa.accept_19_10_2_17_1_675 10 40
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 207 (accept_3_5 8 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 40 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 207 (accept_3_5 5 40 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 207 (Polychromatic418967fa.accept_16_4_8_15_1_1113 4 40 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 207 (Polychromatic418967fa.accept_19_3_2_17_1_6574
  3 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 207 (accept_3_5 2 40
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 207 (Polychromatic418967fa.accept_6_1_4_3_1_14
  1 40 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  207)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 207 (allA_succ_of_accept 38 39 207
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 38 39 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 207 (Polychromatic418967fa.accept_18_1_3_9_1_328 37 39 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 207 3 12 13 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 207 (Polychromatic418967fa.accept_15_5_9_12_1_1599
  35 39 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 207
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 34 39 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 207 3 11 13 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 39 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 207 (Polychromatic418967fa.accept_18_13_3_9_1_4233 31 39
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 207 3 10 13 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 207
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 39 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 39 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 207 3 9 13 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 207 (Polychromatic418967fa.accept_18_8_3_9_1_4232 26 39 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 207
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 39 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 207 3 8 13 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 207 (Polychromatic418967fa.accept_17_6_5_3_1_7134 23 39 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 207 (Polychromatic418967fa.accept_10_2_9_7_1_720 22 39 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 207 3 7 13 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 207
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 39 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 207 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 39 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 207 3 6 13 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 207 (Polychromatic418967fa.accept_20_17_19_7_1_4767 17 39
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 207
  (Polychromatic418967fa.accept_19_16_1_17_1_8065 16 39 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 207 3 5 13 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 39 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 207 (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 39
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 207 3 4 13 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 207
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 39 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 207 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 39 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 207 3 3 13 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 39 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 207
  (Polychromatic418967fa.accept_18_7_3_9_1_1020 7 39 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 207 3 2 13 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 207 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 39 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 207 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 39 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 207 3 1 13 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 207
  (Polychromatic418967fa.accept_10_2_9_7_1_720 2 39 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 207 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 39 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 207))))))))))))))))))))))))))))))))))))))) (allB_succ 38 207
  (allA_succ_of_accept 37 38 207 (accept_3_4 37 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 207 (accept_3_4 34 38 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 207
  (Polychromatic418967fa.accept_27_5_11_18_1_12052 32 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 38 207 (accept_3_4 31 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 38 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 38 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 38 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 207 (accept_3_4 28 38 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27
  38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 207
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 207 (accept_3_4 25 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 207 (Polychromatic418967fa.accept_17_7_4_3_1_3456 24 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 207 (accept_3_4 22 38 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 207 (accept_3_4 19 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 207 (accept_3_4 16 38 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 38 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 207
  (Polychromatic418967fa.accept_21_14_17_18_1_7586 14 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 38 207 (accept_3_4 13 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 38 207 (Polychromatic418967fa.accept_25_12_13_7_1_12051 12 38 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 38 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 38 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 207 (accept_3_4 10 38 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 207 (accept_3_4 7 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  207 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 207 (accept_3_4 4 38 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 38 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 207 (Polychromatic418967fa.accept_20_2_18_7_1_3394
  2 38 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 207 (accept_3_4 1 38
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 207)))))))))))))))))))))))))))))))))))))) (allB_succ 37 207
  (allA_succ_of_accept 36 37 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 37 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 207 (accept_3_5 35 37 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 207 (accept_3_5 32 37
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 207
  (Polychromatic418967fa.accept_19_12_18_17_1_8075 31 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 37 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 207 (accept_3_5 29 37 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 37 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 37 207 (accept_3_5 26 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  37 207 (Polychromatic418967fa.accept_15_10_7_12_1_2490 25 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 37 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 37 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 207 (accept_3_5 23 37 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 37 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 37 207 (accept_3_5 20 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  37 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 37 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 207 (accept_3_5 17 37 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 207
  (Polychromatic418967fa.accept_21_15_16_18_1_7529 15 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 37 207 (accept_3_5 14 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 37 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 37 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 207 (accept_3_5 11 37 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 207 (accept_3_5 8 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  207 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 207 (accept_3_5 5 37 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 207
  (Polychromatic418967fa.accept_15_3_7_12_1_372 3 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 207 (accept_3_5 2 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  207 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 37 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 37 207))))))))))))))))))))))))))))))))))))) (allB_succ 36 207 (allA_succ_of_accept 35 36 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 207 (Polychromatic418967fa.accept_13_8_10_12_1_1337 34 36 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 207 3 11 12 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 207 (Polychromatic418967fa.accept_13_6_10_12_1_2049
  32 36 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 207 3 10 12 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 207 (Polychromatic418967fa.accept_20_9_16_7_1_1129 29 36 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 28 36 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 207 9 3 4 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 36 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 207 (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 36 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 207 3 8 12 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 36 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 207
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 22 36 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 36 207 3 7 12 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 36 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 36 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 207 9 2 4 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 207 (Polychromatic418967fa.accept_21_16_15_18_1_3050 16 36 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 207 3 5 12 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 207 (Polychromatic418967fa.accept_16_14_4_15_1_3944 14 36
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 207
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 36 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 207 3 4 12 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 36 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 36 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 207 9 1 4 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 207
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 36 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 207 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 36 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 207 3 2 12 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 207
  (Polychromatic418967fa.accept_14_4_8_11_1_794 4 36 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 36 207 3 1 12 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 36 207 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 36 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 36 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 207))))))))))))))))))))))))))))))))))))
  (allB_succ 35 207 (allA_succ_of_accept 34 35 207 (accept_3_4 34 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 35 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 207 (accept_3_4 31 35 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 207
  (Polychromatic418967fa.accept_18_12_17_9_1_5513 30 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 35 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 35 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 207 (accept_3_4 28 35 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 35 207 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 35 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 207 (accept_3_4 25 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 207 (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 35 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 207 (accept_3_4 22 35 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 35 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 207 (accept_3_4 19 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 35 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 207 (accept_3_4 16 35 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 35 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 207 (accept_3_4 13 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 207 (Polychromatic418967fa.accept_16_11_3_15_1_1989 11 35 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 207 (accept_3_4 10 35 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 35 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 207 (accept_3_4 7 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 35 207 (Polychromatic418967fa.accept_20_5_15_7_1_7869 5 35 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 207 (accept_3_4 4 35 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 35 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 207 (accept_3_4 1 35 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  207))))))))))))))))))))))))))))))))))) (allB_succ 34 207 (allA_succ_of_accept 33 34 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 207 (accept_3_5 32 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 34 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 207 (accept_3_5 29 34 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 207 (Polychromatic418967fa.accept_16_12_2_15_1_490 28 34 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 207
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 207 (accept_3_5 26 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 34 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 207 (accept_3_5 23 34 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 34 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 207 (accept_3_5 20 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 34 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 207 (accept_3_5 17 34 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 34 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 207
  (Polychromatic418967fa.accept_18_15_16_9_1_4299 15 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 207 (accept_3_5 14 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 34 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 207 (accept_3_5 11 34 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 34 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 207 (accept_3_5 8 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 34 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 207 (accept_3_5 5 34 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 207 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 34 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 34
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 207 (accept_3_5 2 34 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 207))))))))))))))))))))))))))))))))))
  (allB_succ 33 207 (allA_succ_of_accept 32 33 207 (Polychromatic418967fa.accept_13_6_7_12_1_3504 32 33 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 33 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 207 3 10 11 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 33 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 207 (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 33
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 207 3 9 11 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 33 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 207 3 8 11 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 33 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 207 3 7 11 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 33 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 33 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 207 3 6 11 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 33 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 207 3 5 11 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 33 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 207 3 4 11 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 33 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 207 3 3 11 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 33 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 33 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 207 3 2 11 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 33 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 207
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 33 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 207 3 1 11 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 33 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 207)))))))))))))))))))))))))))))))))
  (allB_succ 32 207 (allA_succ_of_accept 31 32 207 (accept_3_4 31 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 32 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 207 (accept_3_4 28 32 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 207
  (Polychromatic418967fa.accept_21_6_11_18_1_10664 27 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 32 207 (Polychromatic418967fa.accept_19_7_13_17_1_8041 26 32 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 32 207 (accept_3_4 25 32 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 32 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 32 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 32 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 32 207 (accept_3_4 22 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  32 207 (Polychromatic418967fa.accept_14_7_4_11_1_3038 21 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 32 207 (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 32 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 32 207 (accept_3_4 19 32 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 32 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 32 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 32 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 32 207 (accept_3_4 16 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  32 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 32 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 32 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 32 207 (accept_3_4 13 32 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 32 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 32 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 32 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 32 207 (accept_3_4 10 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  32 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 32 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 32 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 32 207 (accept_3_4 7 32 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 32 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 32 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 32 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 32 207 (accept_3_4 4 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 32
  207 (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 32 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 32 207 (Polychromatic418967fa.accept_13_2_6_12_1_1334 2 32 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 207 (accept_3_4 1 32 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 207)))))))))))))))))))))))))))))))) (allB_succ 31 207 (allA_succ_of_accept 30 31 207
  (Polychromatic418967fa.accept_13_4_5_12_1_751 30 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 207 (accept_3_5 29 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 31 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 207 (accept_3_5 26 31 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 207 (Polychromatic418967fa.accept_19_6_12_17_1_12050 25 31 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 207
  (Polychromatic418967fa.accept_10_4_1_7_1_371 24 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 207 (accept_3_5 23 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 31 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 207 (accept_3_5 20 31 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 207 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 31 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 207
  (Polychromatic418967fa.accept_19_18_12_17_1_8026 18 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 31 207 (accept_3_5 17 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 31 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 31 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 207 (accept_3_5 14 31 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  31 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 207
  (Polychromatic418967fa.accept_27_12_4_18_1_12049 12 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 31 207 (accept_3_5 11 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 31 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 31 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 207 (accept_3_5 8 31 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 207 (Polychromatic418967fa.accept_13_7_5_12_1_1305
  7 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 207 (accept_3_5 5 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 207 (Polychromatic418967fa.accept_18_3_13_9_1_4260 3 31 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 207 (accept_3_5 2 31 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 31 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 207))))))))))))))))))))))))))))))) (allB_succ 30 207
  (allA_succ_of_accept 29 30 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 30 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 207 3 9 10 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 30 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 207 3 8 10 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 207 (Polychromatic418967fa.accept_14_9_2_11_1_780 23 30 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 207
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 30 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 207 3 7 10 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 30 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 207 3 6 10 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 30 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 207 3 5 10 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 30 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 207 3 4 10 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 207 (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 30 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 30 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 207 3 3 10 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 30 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 30 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 207 3 2 10 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 30 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 207 3 1 10 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 30 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 207)))))))))))))))))))))))))))))) (allB_succ
  29 207 (allA_succ_of_accept 28 29 207 (accept_3_4 28 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 29 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 207 (accept_3_4 25 29 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24
  29 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 207
  (Polychromatic418967fa.accept_19_4_10_17_1_5194 23 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 207 (accept_3_4 22 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 207 (accept_3_4 19 29 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 207 (accept_3_4 16 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 207 (Polychromatic418967fa.accept_13_2_3_12_1_735 15 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 207 (accept_3_4 13 29 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 207
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 29 207 (accept_3_4 10 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 29 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 29 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 207 (accept_3_4 7 29 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 207 (accept_3_4 4 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 29 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 207 (accept_3_4 1 29 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 207))))))))))))))))))))))))))))) (allB_succ 28 207 (allA_succ_of_accept 27 28 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 207 (accept_3_5 26 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 207 (Polychromatic418967fa.accept_16_8_12_15_1_2005 24 28 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 207 (accept_3_5 23 28 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 207 (Polychromatic418967fa.accept_25_22_3_7_1_12048 22 28
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 207
  (Polychromatic418967fa.accept_19_2_9_17_1_626 21 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 207 (accept_3_5 20 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 207 (accept_3_5 17 28 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 207 (Polychromatic418967fa.accept_13_3_2_12_1_2797 16 28 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 207
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 207 (accept_3_5 14 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 207 (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 28 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 207 (accept_3_5 11 28 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 28
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 207
  (Polychromatic418967fa.accept_10_9_8_7_1_714 9 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 207 (accept_3_5 8 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 28 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 207 (accept_3_5 5 28 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 207 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 28 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  28 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 207 (accept_3_5 2 28 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 207))))))))))))))))))))))))))))
  (allB_succ 27 207 (allA_succ_of_accept 26 27 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 27 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 207
  (Polychromatic418967fa.accept_19_6_8_17_1_1524 25 27 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 207 3 8 9 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 27 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 207 (Polychromatic418967fa.accept_19_3_8_17_1_5213 22 27
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 207 3 7 9 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 27 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 27 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 207 9 2 3 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 27 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 27 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 207 3 5 9 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 207 (Polychromatic418967fa.accept_21_14_6_18_1_12047 14 27 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 207 (Polychromatic418967fa.accept_17_13_10_3_1_7136 13 27
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 207 3 4 9 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 207
  (Polychromatic418967fa.accept_13_11_1_12_1_742 11 27 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 27 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 207 9 1 3 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 8 27 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 207
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 27 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 207 3 2 9 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 27 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 27 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 207 3 1 9 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 27 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 207 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 27 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 207))))))))))))))))))))))))))) (allB_succ 26 207 (allA_succ_of_accept 25
  26 207 (accept_3_4 25 26 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 207
  (Polychromatic418967fa.accept_11_2_4_9_1_484 24 26 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 207 (accept_3_4 22 26 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  26 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 207 (accept_3_4 19 26
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 207
  (Polychromatic418967fa.accept_12_6_2_3_1_354 18 26 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 207 (accept_3_4 16 26 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 26 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 207
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 26 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 26 207 (accept_3_4 13 26 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 26 207 (Polychromatic418967fa.accept_20_12_6_7_1_7875 12 26 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 207 (accept_3_4 10 26 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 26 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 207 (accept_3_4 7 26 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 26 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 207 (accept_3_4 4 26 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 26 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  26 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 207 (accept_3_4 1 26 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 207)))))))))))))))))))))))))) (allB_succ 25 207
  (allA_succ_of_accept 24 25 207 (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 25 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 207 (accept_3_5 23 25 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 207 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 207 (accept_3_5 20
  25 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 207
  (Polychromatic418967fa.accept_21_19_4_18_1_10668 19 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 207 (accept_3_5 17 25 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 207
  (Polychromatic418967fa.accept_20_15_5_7_1_4791 15 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 207 (accept_3_5 14 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 25 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 207 (accept_3_5 11 25 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 207 (accept_3_5 8 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  207 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 207 (accept_3_5 5 25 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 207 (accept_3_5 2 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  207 (Polychromatic418967fa.accept_21_1_4_18_1_12046 1 25 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 25 207))))))))))))))))))))))))) (allB_succ 24 207 (allA_succ_of_accept 23 24 207
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 24 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 24 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 207 3 7 8 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 24 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 207
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 24 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 207 3 6 8 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 207 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 24 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 207 (Polychromatic418967fa.accept_17_16_7_3_1_4644 16 24
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 24 207 3 5 8 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 24 207
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 24 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 207 3 4 8 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 24 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 207
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 24 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 24 207 3 3 8 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 24 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 24 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 7
  24 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 207 3 2 8 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 207
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 24 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 24 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 207 3 1 8 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 24 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 207)))))))))))))))))))))))) (allB_succ 23 207 (allA_succ_of_accept 22 23 207 (accept_3_4 22 23 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060
  21 23 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 207 (accept_3_4 19 23 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 23 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 207 (Polychromatic418967fa.accept_27_17_23_18_1_6238 17 23 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 207 (accept_3_4 16 23 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 23 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 207 (accept_3_4 13 23 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 23 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 207 (accept_3_4 10 23 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 207 (accept_3_4 7 23 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  207 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 23 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 207 (accept_3_4 4 23 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 207 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 23 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 207 (accept_3_4 1 23 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 207))))))))))))))))))))))) (allB_succ 22 207
  (allA_succ_of_accept 21 22 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 22 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 207 (accept_3_5 20 22 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 22 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 22 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  18 22 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 207 (accept_3_5 17
  22 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 207
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 22 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 22 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 22 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 207 (accept_3_5 14 22 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 22 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12
  22 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 207 (accept_3_5 11 22
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 10 22 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 22 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 207 (accept_3_5 8 22 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 22 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 207 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  6 22 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 207 (accept_3_5 5 22
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 4 22 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 22 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 22 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 207 (accept_3_5 2 22 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 22 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 207)))))))))))))))))))))) (allB_succ 21 207 (allA_succ_of_accept
  20 21 207 (Polychromatic418967fa.accept_13_7_8_12_1_2810 20 21 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 21 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 21 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 207 3 6 7 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 21 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 21 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 207 3 5 7 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 21 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 207 3 4 7 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 21 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 207 3 3 7 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 21 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 21 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 207 3 2 7 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 21 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 207
  (Polychromatic418967fa.accept_10_4_1_7_1_371 4 21 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 207 3 1 7 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 21 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 207))))))))))))))))))))) (allB_succ 20 207
  (allA_succ_of_accept 19 20 207 (accept_3_4 19 20 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 20 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 207 (accept_3_4 16 20 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 207 (Polychromatic418967fa.accept_19_15_1_17_1_670 15 20 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 207
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 14 20 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 207 (accept_3_4 13 20 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 20 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 207 (accept_3_4 10 20 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 20 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 207
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 8 20 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 207 (accept_3_4 7 20 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 20 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 207 (accept_3_4 4 20 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 20 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 20
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 207 (accept_3_4 1 20 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 207)))))))))))))))))))) (allB_succ 19 207 (allA_succ_of_accept
  18 19 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 19 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 207 (accept_3_5 17 19 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 19 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 207 (accept_3_5 14 19 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  19 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 207 (accept_3_5 11 19 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 19 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 207 (accept_3_5 8 19 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 207 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 19 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 207 (accept_3_5 5 19 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 207 (Polychromatic418967fa.accept_18_3_1_9_1_1929 3 19 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 207 (accept_3_5 2 19 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 207))))))))))))))))))) (allB_succ 18 207 (allA_succ_of_accept 17
  18 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 207 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 18 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 207 3 5 6 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 14
  18 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 207 3 4 6 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 207 (Polychromatic418967fa.accept_19_11_18_17_1_6538 11 18 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 18 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 207 9 1 2 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 18 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 207 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 18 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 207 3 2 6 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 18 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 207 3 1 6 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 18 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 207)))))))))))))))))) (allB_succ 17 207
  (allA_succ_of_accept 16 17 207 (accept_3_4 16 17 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 17 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 207 (accept_3_4 13 17 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 207 (Polychromatic418967fa.accept_18_12_17_9_1_5513 12 17 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 207
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 17 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 207 (accept_3_4 10 17 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 17 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 207 (accept_3_4 7 17 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 207
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 17 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 207 (accept_3_4 4 17 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 17 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 17 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 207 (accept_3_4 1 17 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 17 207))))))))))))))))) (allB_succ 16 207 (allA_succ_of_accept 15 16 207
  (Polychromatic418967fa.accept_13_2_3_12_1_735 15 16 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 207 (accept_3_5 14 16 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 16 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 207 (accept_3_5 11 16 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 207 (Polychromatic418967fa.accept_24_10_16_15_1_12045 10 16 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 207
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 16 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 207 (accept_3_5 8 16 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 16 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 207 (accept_3_5 5 16 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 207 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 16 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3
  16 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 207 (accept_3_5 2 16 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 207)))))))))))))))) (allB_succ 15 207
  (allA_succ_of_accept 14 15 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 14 15 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 15 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 207 3 4 5 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 207
  (Polychromatic418967fa.accept_18_11_15_9_1_360 11 15 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 15 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 207 3 3 5 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 15 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 207
  (Polychromatic418967fa.accept_19_7_15_17_1_5198 7 15 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 207 3 2 5 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 15 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 207 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 15 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 207 3 1 5 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 207
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 15 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 207 (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 15 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 207))))))))))))))) (allB_succ 14 207 (allA_succ_of_accept 13 14 207
  (accept_3_4 13 14 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 14 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 207 (accept_3_4 10 14 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 8
  14 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 207 (accept_3_4 7 14 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 6
  14 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 207 (accept_3_4 4 14 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  207 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 14 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 14 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 207 (accept_3_4 1 14 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 207)))))))))))))) (allB_succ 13 207 (allA_succ_of_accept 12 13 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 207 (accept_3_5 11 13 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 13 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 207 (accept_3_5 8 13 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 13 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 207 (accept_3_5 5 13 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 13 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 207 (accept_3_5 2 13 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 207 (Polychromatic418967fa.accept_15_1_13_12_1_347 1 13 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 207))))))))))))) (allB_succ 12 207 (allA_succ_of_accept 11 12
  207 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 12 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 12 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 207 3 3 4 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 12 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 207
  (Polychromatic418967fa.accept_17_7_12_3_1_4693 7 12 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 207 3 2 4 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 12 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 12 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 207 3 1 4 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 12 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 207)))))))))))) (allB_succ 11 207 (allA_succ_of_accept 10 11 207
  (accept_3_4 10 11 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 207
  (Polychromatic418967fa.accept_12_9_11_3_1_772 9 11 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 207 (accept_3_4 7 11 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 207 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 11 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 207 (Polychromatic418967fa.accept_19_5_11_17_1_6536
  5 11 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 207 (accept_3_4 4 11
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 207
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 11 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 11 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 207 (accept_3_4 1 11 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 11 207))))))))))) (allB_succ 10 207 (allA_succ_of_accept 9 10 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 207 (accept_3_5 8 10 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 10 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 207 (accept_3_5 5 10 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 207 (Polychromatic418967fa.accept_19_4_10_17_1_5194 4 10 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 207 (Polychromatic418967fa.accept_20_3_10_7_1_7839
  3 10 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 207 (accept_3_5 2 10
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  10 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 207)))))))))) (allB_succ 9 207
  (allA_succ_of_accept 8 9 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 9 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 207 3 2 3 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 207 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 9 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 207 3 1 3 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 9 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 207))))))))) (allB_succ 8 207 (allA_succ_of_accept 7 8 207 (accept_3_4 7 8 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 8 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 207 (accept_3_4 4 8 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 8 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 207 (Polychromatic418967fa.accept_24_2_8_15_1_10536 2 8 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 207 (accept_3_4 1 8 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 207)))))))) (allB_succ 7 207 (allA_succ_of_accept 6 7 207
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 7 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 207 (accept_3_5 5 7 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 207
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 207 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 7 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 207 (accept_3_5 2 7 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 207 (Polychromatic418967fa.accept_29_1_7_4_1_12044 1 7 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 207))))))) (allB_succ 6 207 (allA_succ_of_accept 5 6 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 6 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 207 3 1 2 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 6 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 207)))))) (allB_succ 5 207 (allA_succ_of_accept 4 5 207 (accept_3_4 4 5 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 5 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 207 (accept_3_4 1 5 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 207))))) (allB_succ 4 207 (allA_succ_of_accept 3 4 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 4 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 207 (accept_3_5 2 4 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 207
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 207)))) (allB_succ 3 207 (allA_succ_of_accept 2 3 207 (Polychromatic418967fa.accept_13_2_3_12_1_735 2 3
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 3 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 207))) (allB_succ 2 207 (allA_succ_of_accept 1 2 207 (accept_3_4 1 2 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 207)) (allB_two
  207))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


