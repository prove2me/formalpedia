-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch287_Segment001
-- name    : Polychromatic418967fa_Branch287_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:57:36.406669+00:00
-- url     : https://prove2.me/theorems/4af79540-d562-40b4-bbbb-8080930fad18
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch287_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_287_segment_001 : allB 180 287 :=
  allB_succ' 109 179 287 (Eq.refl Bool.true) (allA_succ_of_accept 108 179 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 108 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 179 287 (Polychromatic418967fa.accept_16_11_3_15_1_1989 107 179 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 179 287 (accept_3_2 106 179 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 179 287 (Polychromatic418967fa.accept_19_10_8_2_1_831 105 179 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 179 287
  (Polychromatic418967fa.accept_21_20_11_14_1_5718 104 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 179 287 (accept_3_2 103 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 179 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 102 179 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 179 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 101 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 179 287 (accept_3_2 100 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 179 287
  (Polychromatic418967fa.accept_22_11_3_1_1_3481 99 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 179 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 98 179 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 179 287 (accept_3_2 97 179 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 179 287 (Polychromatic418967fa.accept_19_1_8_2_1_2876 96 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 179 287
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 95 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 179 287 (accept_3_2 94 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 179 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 93 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 179 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 92 179 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 179 287 (accept_3_2 91 179 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 179 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 90 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 179 287
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 89 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 179 287 (accept_3_2 88 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 179 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 87 179 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 179 287 (Polychromatic418967fa.accept_17_1_9_15_1_3186 86 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 179 287 (accept_3_2 85 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 179 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 84 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 179 287 (Polychromatic418967fa.accept_21_20_11_14_1_5718 83 179 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 179 287 (accept_3_2 82 179 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 179 287 (Polychromatic418967fa.accept_19_5_8_2_1_1707 81 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 179 287
  (Polychromatic418967fa.accept_14_10_11_7_1_1955 80 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 179 287 (accept_3_2 79 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 179 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 78 179 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 179 287 (Polychromatic418967fa.accept_16_13_3_15_1_1931 77 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 179 287 (accept_3_2 76 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 179 287
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 75 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 179 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 74 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 179 287 (accept_3_2 73 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 179 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 179 287
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 71 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 179 287 (accept_3_2 70 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 179 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 69 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 179 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 179 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 179 287 (accept_3_2 67 179 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 179 287 (Polychromatic418967fa.accept_14_10_11_7_1_1955 66 179 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 179 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 179 287 (accept_3_2 64 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 179 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 63 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 179 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 62 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 179 287 (accept_3_2 61 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 179 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 179 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 179 287
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 59 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 179 287 (accept_3_2 58 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 179 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 179 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 56 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 179 287 (accept_3_2 55 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 179 287 (Polychromatic418967fa.accept_21_12_11_14_1_7239 54
  179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 179 287
  (Polychromatic418967fa.accept_19_15_8_2_1_4110 53 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 179 287 (accept_3_2 52 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 179 287 (Polychromatic418967fa.accept_19_13_8_2_1_4089 51 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 179 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 50 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 179 287 (accept_3_2 49 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 179 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 287
  (Polychromatic418967fa.accept_21_5_11_14_1_7219 47 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 179 287 (accept_3_2 46 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 179 287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 179 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 179 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 287 (accept_3_2 43 179 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 179 287 (Polychromatic418967fa.accept_10_2_9_7_1_720
  42 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 287
  (Polychromatic418967fa.accept_17_7_9_15_1_8105 41 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 179 287 (accept_3_2 40 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 179 287 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 179 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 38 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 287 (accept_3_2 37 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 179 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 179 287 (accept_3_2 34 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 179 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 33 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 179 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 287 (accept_3_2 31 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 287
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 29 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 179 287 (accept_3_2 28 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 179 287 (Polychromatic418967fa.accept_15_12_14_2_1_3794 27 179 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 287
  (Polychromatic418967fa.accept_20_6_19_7_1_3375 26 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 287 (accept_3_2 25 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 287 (Polychromatic418967fa.accept_16_7_3_15_1_2940 23 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 287 (accept_3_2 22 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 287 (Polychromatic418967fa.accept_28_21_11_7_1_17649 21
  179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 287 (accept_3_2 19 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 287 (accept_3_2 16 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 287 (Polychromatic418967fa.accept_19_15_8_2_1_4110 15 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 287
  (Polychromatic418967fa.accept_19_14_8_2_1_6846 14 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 287 (accept_3_2 13 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 287 (accept_3_2 10 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 287
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 287 (accept_3_2 7 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 287 (Polychromatic418967fa.accept_17_6_9_15_1_3185 6 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 287 (accept_3_2 4 179 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 3 179
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 287
  (Polychromatic418967fa.accept_10_2_9_7_1_720 2 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 287 (accept_3_2 1 179 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 178 287 (Eq.refl Bool.true) (allA_of_3_0 110 178 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 177 287 (Eq.refl Bool.true) (allA_succ_of_accept 110 177 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 177 287 (accept_3_2 109 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 177 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 108 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 177 287 (Polychromatic418967fa.accept_16_11_1_15_1_1123 107 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 177 287 (accept_3_2 106 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 177 287 (Polychromatic418967fa.accept_19_10_6_2_1_6907 105
  177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 177 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 104 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 177 287 (accept_3_2 103 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 177 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 177 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 101 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 177 287 (accept_3_2 100 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 177 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 177
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 177 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 177 287 (accept_3_2 97 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 177 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 96 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 177 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 95 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 177 287 (accept_3_2 94 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 177 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 177 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 177 287 (accept_3_2 91 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 177 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 177 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 89 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 177 287 (accept_3_2 88 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 177 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 87 177
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 177 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 177 287 (accept_3_2 85 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 177 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 177 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 177 287 (accept_3_2 82 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 177 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 81 177 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 177 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 177 287 (accept_3_2 79 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 177 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 177 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 177 287 (accept_3_2 76 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 177 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 177 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 177 287 (accept_3_2 73 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 177 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 72 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 177 287 (Polychromatic418967fa.accept_13_6_8_1_1_2913 71 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 177 287 (accept_3_2 70 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 177 287 (Polychromatic418967fa.accept_16_5_1_15_1_3922 69 177
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 177 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 177 287 (accept_3_2 67 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 177 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 177 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 287 (accept_3_2 64 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 177 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 177 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 177 287 (accept_3_2 61 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 177 287 (Polychromatic418967fa.accept_17_9_7_15_1_4346 60 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 177 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 287 (accept_3_2 58 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 177 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 177 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 177 287 (accept_3_2 55 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 177 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 177 287 (Polychromatic418967fa.accept_16_5_1_15_1_3922 53 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 287 (accept_3_2 52 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 177 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 177
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 177 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 177 287 (accept_3_2 49 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 177 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 177 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 287 (accept_3_2 46 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 287 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 177 287 (accept_3_2 43 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 177 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 177 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 287 (accept_3_2 40 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 177 287 (accept_3_2 37 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 177 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 177 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 35 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 287 (accept_3_2 34 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 177
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 177 287 (accept_3_2 31 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 177 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 177 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 287 (accept_3_2 28 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 287 (accept_3_2 25 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 177 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 177 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 287 (accept_3_2 22 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 287 (accept_3_2 19 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 177 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 177 287 (Polychromatic418967fa.accept_21_17_9_14_1_5700 17 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 287 (accept_3_2 16 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 177
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 287 (accept_3_2 13 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 177 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 177 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 287 (accept_3_2 10 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 287 (accept_3_2 7 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  177 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 177 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 287 (accept_3_2 4 177 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 177 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 287 (accept_3_2 1 177 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 176 287 (Eq.refl Bool.true) (allA_succ_of_accept 111 176 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 176 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 176 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 176 287 (accept_3_2 109 176 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 176 287 (Polychromatic418967fa.accept_21_3_8_14_1_8864 108 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 176 287
  (Polychromatic418967fa.accept_13_3_7_1_1_334 107 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 176 287 (accept_3_2 106 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 176 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 104 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 176 287 (accept_3_2 103 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 176 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 176
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 176 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 101 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 176 287 (accept_3_2 100 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 176 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 98 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 176 287 (accept_3_2 97 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 176 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 176 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 95 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 176 287 (accept_3_2 94 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 176 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 176 287 (accept_3_2 91 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 176 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 90 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 176 287
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 89 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 176 287 (accept_3_2 88 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 176 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 86 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 176 287 (accept_3_2 85 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 176 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 176 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 176 287 (accept_3_2 82 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 176 287 (Polychromatic418967fa.accept_15_5_11_2_1_1095 80 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 176 287 (accept_3_2 79 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 176 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 176 287
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 77 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 176 287 (accept_3_2 76 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 176 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 176 287 (accept_3_2 73 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 176 287 (Polychromatic418967fa.accept_23_3_15_11_1_17648 72 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 176 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 71 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 176 287 (accept_3_2 70 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 176 287 (Polychromatic418967fa.accept_13_3_7_1_1_334 68 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 176 287 (accept_3_2 67 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 176 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 176 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 176 287 (accept_3_2 64 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 176 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 62 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 176 287 (accept_3_2 61 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 176 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 176 287
  (Polychromatic418967fa.accept_17_8_6_15_1_523 59 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 176 287 (accept_3_2 58 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 176 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 176 287 (accept_3_2 55 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 176 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 176 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 53 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 176 287 (accept_3_2 52 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 176 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 176 287 (accept_3_2 49 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 176 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 176 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 176 287 (accept_3_2 46 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 176 287 (Polychromatic418967fa.accept_21_2_8_14_1_4148 44 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 176 287 (accept_3_2 43 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 176 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 176 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 41 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 176 287 (accept_3_2 40 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 176 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 176 287 (accept_3_2 37 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 176 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 36 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 176 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 176 287 (accept_3_2 34 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 176 287 (Polychromatic418967fa.accept_13_6_7_1_1_335 32 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 176 287 (accept_3_2 31 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 176 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 176 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 176 287 (accept_3_2 28 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 176 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 176 287 (accept_3_2 25 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 176 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 176 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 176 287 (accept_3_2 22 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 176 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 176 287 (accept_3_2 19 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 176 287 (Polychromatic418967fa.accept_19_18_5_2_1_8352 18 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 176 287
  (Polychromatic418967fa.accept_19_17_5_2_1_2843 17 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 176 287 (accept_3_2 16 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 176 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 176 287 (accept_3_2 13 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 176 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 176 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 176 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 176 287 (accept_3_2 10 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 176 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 176 287 (accept_3_2 7 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 176 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 176 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 176 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 176 287 (accept_3_2 4 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  176 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 176 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 176 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 176 287 (accept_3_2 1 176 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 175 287 (Eq.refl Bool.true) (allA_of_3_0 113 175 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 114 174 287 (Eq.refl Bool.true) (allA_succ_of_accept 113 174 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  113 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 174 287 (accept_3_2
  112 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 174 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 111 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 174 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 110 174 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 174 287 (accept_3_2 109 174 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 174 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 108 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 174 287
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 107 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 174 287 (accept_3_2 106 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 174 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 174 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 104 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 174 287 (accept_3_2 103 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 174 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 102 174
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 174 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 174 287 (accept_3_2 100 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 174 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 99 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 174 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 98 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 174 287 (accept_3_2 97 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 174 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 174 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 174 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 95 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 174 287 (accept_3_2 94 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 174 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 174 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 92 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 174 287 (accept_3_2 91 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 174 287 (Polychromatic418967fa.accept_13_12_5_1_1_1383 90 174 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 174 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 174 287 (accept_3_2 88 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 174 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 174 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 86 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 174 287 (accept_3_2 85 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 174 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 84 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 174 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 174 287 (accept_3_2 82 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 174 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 174 287 (Polychromatic418967fa.accept_22_14_20_1_1_6722 80 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 174 287 (accept_3_2 79 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 174 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 174 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 174 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 174 287 (accept_3_2 76 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 174 287 (Polychromatic418967fa.accept_19_18_3_2_1_6939 75 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 174 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 174 287 (accept_3_2 73 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 174 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 174 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 71 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 174 287 (accept_3_2 70 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 174 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 174 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 174 287 (accept_3_2 67 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 174 287 (Polychromatic418967fa.accept_21_3_6_14_1_5717 66 174 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 174 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 174 287 (accept_3_2 64 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 174 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 174 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 174 287 (accept_3_2 61 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 174 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 174 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 174 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 174 287 (accept_3_2 58 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 174 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 174 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 174 287 (accept_3_2 55 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 174 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 174 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 174 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 174 287 (accept_3_2 52 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 174 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 174 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 174 287 (accept_3_2 49 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 174 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 174 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 174 287 (accept_3_2 46 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 174 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 174 287 (Polychromatic418967fa.accept_17_10_4_15_1_2165 44 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 174 287 (accept_3_2 43 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 174 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 174 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 174 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 174 287 (accept_3_2 40 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 174 287 (Polychromatic418967fa.accept_16_7_14_15_1_2932 39 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 174 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 287 (accept_3_2 37 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 174 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 174 287
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 174 287 (accept_3_2 34 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 174 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 174 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 287 (accept_3_2 31 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 174 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 30 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 174 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 174 287 (accept_3_2 28 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 174 287 (Polychromatic418967fa.accept_14_13_6_7_1_2013 27 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 174 287 (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 287 (accept_3_2 25 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 174 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 174 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 174 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 174 287 (accept_3_2 22 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 174 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 174 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 287 (accept_3_2 19 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 287 (Polychromatic418967fa.accept_19_18_3_2_1_6939 18 174 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 174 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 174 287 (accept_3_2 16 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 174 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 174 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 287 (accept_3_2 13 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 174 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 174 287 (accept_3_2 10 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  174 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 174 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 287 (accept_3_2 7 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 174 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 174 287 (accept_3_2 4 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  174 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 174 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 174 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 287 (accept_3_2 1 174 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 174
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 173 287 (Eq.refl Bool.true) (allA_succ_of_accept 114 173 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 114 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 173 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 113 173 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 173 287 (accept_3_2 112 173 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 173 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 111 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 173 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 173 287 (accept_3_2 109 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 173 287 (Polychromatic418967fa.accept_16_12_13_15_1_1966 108 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 173 287 (Polychromatic418967fa.accept_13_3_4_1_1_363 107 173 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 173 287 (accept_3_2 106 173 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 173 287 (Polychromatic418967fa.accept_9_6_2_8_1_592
  105 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 173 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 104 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 173 287 (accept_3_2 103 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 173 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 101 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 173 287 (accept_3_2 100 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 173 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 99 173
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 173 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 173 287 (accept_3_2 97 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 173 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 173 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 173 287 (accept_3_2 94 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 173 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 173 287
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 92 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 173 287 (accept_3_2 91 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 173 287 (Polychromatic418967fa.accept_23_20_12_11_1_6119 89 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 173 287 (accept_3_2 88 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 173 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 173 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 173 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 173 287 (accept_3_2 85 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 173 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 173 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 83 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 173 287 (accept_3_2 82 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 173 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 173
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 173 287
  (Polychromatic418967fa.accept_17_12_3_15_1_5476 80 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 173 287 (accept_3_2 79 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 173 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 173 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 173 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 173 287 (accept_3_2 76 173 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 173 287 (Polychromatic418967fa.accept_9_3_2_8_1_108
  75 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 173 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 173 287 (accept_3_2 73 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 173 287 (Polychromatic418967fa.accept_14_2_5_7_1_3767 72 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 173 287 (Polychromatic418967fa.accept_21_8_5_14_1_5660 71 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 173 287 (accept_3_2 70 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 173 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 173 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 173 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 173 287 (accept_3_2 67 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 173 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 173 287 (accept_3_2 64 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 173 287 (Polychromatic418967fa.accept_17_12_3_15_1_5476 63 173
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 173 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 173 287 (accept_3_2 61 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 173 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 173 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 173 287 (accept_3_2 58 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 173 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 287
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 56 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 173 287 (accept_3_2 55 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 173 287 (Polychromatic418967fa.accept_21_11_5_14_1_4142 53 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 173 287 (accept_3_2 52 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 173 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 173 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 287 (accept_3_2 49 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 287 (Polychromatic418967fa.accept_23_1_12_11_1_17647 47 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 287 (accept_3_2 46 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 173
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 287
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 287 (accept_3_2 43 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 287 (accept_3_2 40 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 287 (accept_3_2 37 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 287 (accept_3_2 34 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 173 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 287 (accept_3_2 31 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 287 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 287 (accept_3_2 28 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 287 (Polychromatic418967fa.accept_23_4_12_11_1_17646 27
  173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 287 (accept_3_2 25 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 287 (accept_3_2 22 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 173 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 287
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 20 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 173 287 (accept_3_2 19 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 173 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 287 (Polychromatic418967fa.accept_21_17_5_14_1_4144 17 173
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 287 (accept_3_2 16 173
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 173 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 287 (accept_3_2 13 173 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 173 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 287
  (Polychromatic418967fa.accept_21_11_5_14_1_4142 11 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 173 287 (accept_3_2 10 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 173 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 173 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 287 (Polychromatic418967fa.accept_21_8_5_14_1_5660 8 173
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 287 (accept_3_2 7 173 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 287 (accept_3_2 4 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 173 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 287 (accept_3_2 1 173 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 172 287 (Eq.refl Bool.true) (allA_of_3_0 116 172 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 117 171 287 (Eq.refl Bool.true) (allA_succ_of_accept 116 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 116 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 171 287 (accept_3_2 115 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 171 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 114 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 171 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 113 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 171 287 (accept_3_2 112 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 171 287 (Polychromatic418967fa.accept_17_9_1_15_1_3156 111
  171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 110 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 171 287 (accept_3_2 109 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 171 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 108 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 171 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 107 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 171 287 (accept_3_2 106 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 171 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 105
  171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 104 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 171 287 (accept_3_2 103 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 171 287 (Polychromatic418967fa.accept_14_4_3_7_1_3702 102 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 171 287 (Polychromatic418967fa.accept_15_11_6_2_1_1106 101 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 171 287 (accept_3_2 100 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 171 287 (Polychromatic418967fa.accept_16_3_11_15_1_1963 99 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 98 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 171 287 (accept_3_2 97 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 171 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 96 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 171 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 95 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 171 287 (accept_3_2 94 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 171 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 93 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 171 287 (accept_3_2 91 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 171 287 (Polychromatic418967fa.accept_13_12_2_1_1_2909 90 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 171 287 (Polychromatic418967fa.accept_23_20_10_11_1_12965 89 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 171 287 (accept_3_2 88 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 171 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 87 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 171 287 (accept_3_2 85 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 171 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 171 287 (Polychromatic418967fa.accept_15_8_6_2_1_1128 83 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 171 287 (accept_3_2 82 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 171 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 171 287 (accept_3_2 79 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 171 287 (Polychromatic418967fa.accept_20_18_11_7_1_6344 78 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 171 287 (Polychromatic418967fa.accept_13_12_2_1_1_2909 77 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 171 287 (accept_3_2 76 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 171 287 (Polychromatic418967fa.accept_21_12_3_14_1_10498 75
  171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 171 287 (accept_3_2 73 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 171 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 72 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 171 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 287 (accept_3_2 70 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 171 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 171 287 (accept_3_2 67 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 171 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 66 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 171 287 (Polychromatic418967fa.accept_16_1_11_15_1_498 65 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 287 (accept_3_2 64 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 171 287 (Polychromatic418967fa.accept_17_12_1_15_1_5472 63 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 171 287 (accept_3_2 61 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 171 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 171 287 (Polychromatic418967fa.accept_21_17_3_14_1_2807 59 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 287 (accept_3_2 58 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 171 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 171 287 (accept_3_2 55 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 171 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 171 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 53 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 287 (accept_3_2 52 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 171 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 171 287 (accept_3_2 49 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 171 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 48 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 171 287 (Polychromatic418967fa.accept_23_1_10_11_1_17645 47 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 287 (accept_3_2 46 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 171 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 171 287 (accept_3_2 43 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 171 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 42 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 171 287 (Polychromatic418967fa.accept_15_11_6_2_1_1106 41 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 287 (accept_3_2 40 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 39 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 171 287 (accept_3_2 37 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 171 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 171 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 35 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 287 (accept_3_2 34 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 287 (accept_3_2 31 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 171 287 (Polychromatic418967fa.accept_18_12_9_17_1_7428 30 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 171 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 287 (accept_3_2 28 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 287 (accept_3_2 25 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 171 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 171 287 (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 287 (accept_3_2 22 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 287 (accept_3_2 19 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 171 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 171 287 (Polychromatic418967fa.accept_16_1_11_15_1_498 17 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 287 (accept_3_2 16 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 287 (Polychromatic418967fa.accept_18_15_9_17_1_6043 15 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 287 (accept_3_2 13 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 171 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 171 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 287 (accept_3_2 10 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 171
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 287 (accept_3_2 7 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  171 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 171 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 171 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 287 (accept_3_2 4 171 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 171 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 287 (accept_3_2 1 171 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 170 287 (Eq.refl Bool.true) (allA_succ_of_accept 117 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  117 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 170 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 116 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 170 287 (accept_3_2 115 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 170 287 (Polychromatic418967fa.accept_21_9_2_14_1_7251 114 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 113 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 113 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 170 287 (accept_3_2 112 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 170 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 111 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 170 287
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 110 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 170 287 (accept_3_2 109 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 170 287 (Polychromatic418967fa.accept_15_3_5_2_1_2816 108 170 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 170 287
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 107 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 170 287 (accept_3_2 106 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 170 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 104 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 170 287 (accept_3_2 103 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 170 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 102
  170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 170 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 170 287 (accept_3_2 100 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 170 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 170 287 (Polychromatic418967fa.accept_19_3_18_2_1_6935 98 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 170 287 (accept_3_2 97 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 170 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 96 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 170 287
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 95 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 170 287 (accept_3_2 94 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 170 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 92 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 170 287 (accept_3_2 91 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 170 287 (Polychromatic418967fa.accept_21_6_2_14_1_5688 90 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 170 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 170 287 (accept_3_2 88 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 170 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 170 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 86 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 170 287 (accept_3_2 85 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 170 287 (Polychromatic418967fa.accept_25_9_20_12_1_17620 84
  170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 170 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 83 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 170 287 (accept_3_2 82 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 170 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 80 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 170 287 (accept_3_2 79 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 170 287 (Polychromatic418967fa.accept_15_3_5_2_1_2816 78 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 170 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 170 287 (accept_3_2 76 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 170 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 170 287 (Polychromatic418967fa.accept_15_14_5_2_1_4761 74 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 170 287 (accept_3_2 73 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 170 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 170 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 71 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 170 287 (accept_3_2 70 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 170 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 68 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 170 287 (accept_3_2 67 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 170 287 (Polychromatic418967fa.accept_19_9_18_2_1_8383 66 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 170 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 170 287 (accept_3_2 64 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 170 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 170 287 (Polychromatic418967fa.accept_16_14_10_15_1_3969 62 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 170 287 (accept_3_2 61 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 170 287 (Polychromatic418967fa.accept_19_3_18_2_1_6935 60 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 170 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 59 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 170 287 (accept_3_2 58 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 170 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 170 287 (accept_3_2 55 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 170 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 54 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 170 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 170 287 (accept_3_2 52 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 170 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 170 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 170 287 (accept_3_2 49 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 170 287 (Polychromatic418967fa.accept_15_3_5_2_1_2816 48 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 170 287
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 47 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 170 287 (accept_3_2 46 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 170 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 170 287 (accept_3_2 43 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 170 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 42 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 170 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 170 287 (accept_3_2 40 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 170 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 170 287 (Polychromatic418967fa.accept_18_2_8_17_1_4754 38 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 170 287 (accept_3_2 37 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 170 287 (Polychromatic418967fa.accept_23_13_9_11_1_4514 36 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 170 287
  (Polychromatic418967fa.accept_19_16_18_2_1_6934 35 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 170 287 (accept_3_2 34 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 170 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 170 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 170 287 (accept_3_2 31 170
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 170 287
  (Polychromatic418967fa.accept_16_14_10_15_1_3969 30 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 170 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 170 287 (accept_3_2 28 170 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 170 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 287
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 170 287 (accept_3_2 25 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 170 287 (Polychromatic418967fa.accept_19_5_18_2_1_5404 24 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 170 287 (Polychromatic418967fa.accept_14_9_2_7_1_1242 23 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 287 (accept_3_2 22 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 170 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 170 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 170 287 (accept_3_2 19 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 170 287 (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 170 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 287 (accept_3_2 16 170 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 170 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 170 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 14 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 170 287 (accept_3_2 13 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 170 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 170 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 287 (accept_3_2 10 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 170 287 (accept_3_2 7 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  170 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 170 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 170 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 287 (accept_3_2 4 170 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 170 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 287
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 2 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 287 (accept_3_2 1 170 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 169 287 (Eq.refl Bool.true) (allA_of_3_0 119 169 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 120 168 287 (Eq.refl Bool.true) (allA_succ_of_gcd 119 168 287 7 17 24 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 118 168 287 (accept_3_2 118 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 168 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 117
  168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 168 287
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 116 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 168 287 (accept_3_2 115 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 168 287 (Polychromatic418967fa.accept_23_22_7_11_1_7954 114 168 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 168 287 (Polychromatic418967fa.accept_9_5_6_8_1_101
  113 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 168 287 7 16 24 41
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 168 287
  (Polychromatic418967fa.accept_9_3_6_8_1_308 111 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 168 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 110 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 168 287 (accept_3_2 109 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 168 287 (Polychromatic418967fa.accept_16_12_8_15_1_5119 108 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 168 287
  (Polychromatic418967fa.accept_25_7_18_12_1_12545 107 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 168 287 (accept_3_2 106 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 168 287 7 15 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 168 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 104 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 168 287 (accept_3_2 103 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 168 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 168
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 168 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 168 287 (accept_3_2 100 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 168 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 99 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 168 287 7 14 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 168 287 (accept_3_2 97 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 168 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 96 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 168 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 95 168 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 168 287 (accept_3_2 94 168 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 168 287 (Polychromatic418967fa.accept_9_3_6_8_1_308
  93 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 168 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 92 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 91 168 287 7 13 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 90 168 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 90 168 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 168 287 (Polychromatic418967fa.accept_10_9_8_7_1_714
  89 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 168 287 (accept_3_2 88
  168 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 168 287
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 87 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 168 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 168 287 (accept_3_2 85 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 168 287 7 12 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 168 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 168 287 (accept_3_2 82 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 168 287 (Polychromatic418967fa.accept_16_1_8_15_1_1945 81 168
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 168 287
  (Polychromatic418967fa.accept_13_2_12_1_1_343 80 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 168 287 (accept_3_2 79 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 168 287 (Polychromatic418967fa.accept_23_9_7_11_1_17644 78 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 77 168 287 7 11 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 168 287 (accept_3_2 76 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 168 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 168 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 168 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 168 287 (accept_3_2 73 168 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 168 287
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 168 287 (Polychromatic418967fa.accept_16_7_8_15_1_6327 71 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 168 287 7 10 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 168 287 (Polychromatic418967fa.accept_10_9_8_7_1_714
  69 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 168 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 168 287 (accept_3_2 67 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 168 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 168 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 168 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 168 287 (accept_3_2 64 168 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 63 168 287 7 9 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 168 287 (Polychromatic418967fa.accept_19_5_16_2_1_1717 62 168
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 168 287 (accept_3_2 61 168
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 168 287
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 60 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 168 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 168 287 (accept_3_2 58 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 168 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 168 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 168 287 7 8 24 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 287 (accept_3_2 55 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 168 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 54 168
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 168 287
  (Polychromatic418967fa.accept_22_9_14_1_1_14670 53 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 168 287 (accept_3_2 52 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 168 287 (Polychromatic418967fa.accept_18_15_6_17_1_2386 51 168 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 168 287 (Polychromatic418967fa.accept_9_5_6_8_1_101
  50 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 168 287 7 7 24 41
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 168 287
  (Polychromatic418967fa.accept_9_3_6_8_1_308 48 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 168 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 168 287 (accept_3_2 46 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 168 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 168 287
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 44 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 168 287 (accept_3_2 43 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  168 287 7 6 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 168 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 168 287 (accept_3_2 40 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 168 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 168 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 168 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 287 (accept_3_2 37 168 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 168 287
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 168 287 7 5 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 168 287 (accept_3_2 34 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 168 287 (Polychromatic418967fa.accept_16_1_8_15_1_1945 33 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 168 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 168 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 287 (accept_3_2 31 168 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 168 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 168 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 287 7 4 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 168 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 168 287 (Polychromatic418967fa.accept_19_7_16_2_1_6953 26 168
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 287 (accept_3_2 25 168
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 24 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 168 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 168 287 (accept_3_2 22 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 168 287 7 3 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 168 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 287 (accept_3_2 19 168 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 168
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 287
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 17 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 287 (accept_3_2 16 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 168 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 168 287 7 2 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 287 (accept_3_2 13 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 168 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 168 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 287 (accept_3_2 10 168 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 9
  168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 287
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 168 287 7 1 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 168 287 (Polychromatic418967fa.accept_25_6_18_12_1_17643 6 168 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 168 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 287 (accept_3_2 4 168 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 168 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 168 287 (accept_3_2 1 168 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 167 287 (Eq.refl Bool.true) (allA_succ_of_accept 120 167 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 120 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 167 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 119 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 167 287 (accept_3_2 118 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 167 287 (Polychromatic418967fa.accept_27_9_5_17_1_17642 117 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 167 287
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 116 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 167 287 (accept_3_2 115 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 114 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 167 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 113 167
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 167 287 (accept_3_2 112 167
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 167 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 111 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 167 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 167 287 (accept_3_2 109 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 167 287 (Polychromatic418967fa.accept_17_6_14_15_1_5505 108 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 167 287
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 107 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 167 287 (accept_3_2 106 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 105 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 167 287 (Polychromatic418967fa.accept_14_6_13_7_1_2015 104
  167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 167 287 (accept_3_2 103
  167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 167 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 102 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 167 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 167 287 (accept_3_2 100 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 167 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 99 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 167 287
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 98 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 167 287 (accept_3_2 97 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 167 287 (Polychromatic418967fa.accept_21_11_20_14_1_4179 95 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 167 287 (accept_3_2 94 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 167 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 167 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 167 287 (accept_3_2 91 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 167 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 90 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 167 287 (Polychromatic418967fa.accept_19_13_15_2_1_4126 89 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 167 287 (accept_3_2 88 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 167 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 86 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 167 287 (accept_3_2 85 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 167 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 167 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 167 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 167 287 (accept_3_2 82 167 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 167 287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 81 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 167 287
  (Polychromatic418967fa.accept_11_3_2_1_1_994 80 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 167 287 (accept_3_2 79 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 167 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 77 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 167 287 (accept_3_2 76 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 167 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 167 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 167 287 (accept_3_2 73 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 167 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 167 287 (Polychromatic418967fa.accept_14_1_13_7_1_1205 71 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 167 287 (accept_3_2 70 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 167 287
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 68 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 167 287 (accept_3_2 67 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 167 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 167 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 167 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 167 287 (accept_3_2 64 167 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 167 287 (Polychromatic418967fa.accept_17_12_14_15_1_5561 63 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 167 287
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 62 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 167 287 (accept_3_2 61 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 59 167
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 287 (accept_3_2 58 167
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 167 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 287 (accept_3_2 55 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 167 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 287
  (Polychromatic418967fa.accept_21_11_20_14_1_4179 53 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 167 287 (accept_3_2 52 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 287 (Polychromatic418967fa.accept_14_8_13_7_1_2798 50 167
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 287 (accept_3_2 49 167
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 167 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 287 (accept_3_2 46 167 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 167 287 (Polychromatic418967fa.accept_25_20_17_12_1_17641 45 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 287
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 44 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 287 (accept_3_2 43 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 287 (Polychromatic418967fa.accept_23_18_6_11_1_14518 41 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 287 (accept_3_2 40 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 287 (accept_3_2 37 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 287 (accept_3_2 34 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 287
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 287 (accept_3_2 31 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 167 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 287 (accept_3_2 28 167 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 287 (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 287
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 26 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 287 (accept_3_2 25 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 287 (accept_3_2 22 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 287 (accept_3_2 19 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 287 (Polychromatic418967fa.accept_19_18_15_2_1_11128 18 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 287 (Polychromatic418967fa.accept_19_17_15_2_1_6887 17 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 287 (accept_3_2 16 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598
  15 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 287
  (Polychromatic418967fa.accept_11_3_2_1_1_994 14 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 287 (accept_3_2 13 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 167 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 287 (accept_3_2 10 167 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 287 (accept_3_2 7 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 287 (Polychromatic418967fa.accept_21_5_20_14_1_4162 5 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 287 (accept_3_2 4 167 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 167 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 287 (accept_3_2 1 167 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 166 287 (Eq.refl Bool.true) (allA_of_3_0 122 166 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 123 165 287 (Eq.refl Bool.true) (allA_succ_of_accept 122 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 122 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 165 287 (accept_3_2 121 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 165 287 (Polychromatic418967fa.accept_17_1_12_15_1_1263 120 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 119 165 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 119 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 165 287 (accept_3_2 118 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 165 287 (Polychromatic418967fa.accept_21_12_18_14_1_8854 117
  165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 165 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 116 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 165 287 (accept_3_2 115 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 165 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 165 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 113 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 165 287 (accept_3_2 112 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 165 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 111 165
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 165 287 (accept_3_2 109 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 165 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 108 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 165 287 (Polychromatic418967fa.accept_22_19_11_1_1_13116 107 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 165 287 (accept_3_2 106 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 165 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 165
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 165 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 104 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 165 287 (accept_3_2 103 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 165 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 165 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 165 287 (accept_3_2 100 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 165 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 165
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 165 287 (accept_3_2 97 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 165 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 165 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 165 287 (accept_3_2 94 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 165 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 93 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 165 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 165 287 (accept_3_2 91 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 165 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 165 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 89 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 165 287 (accept_3_2 88 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 165 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 165 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 165 287 (accept_3_2 85 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 165 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 84 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 165 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 165 287 (accept_3_2 82 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 165 287 (Polychromatic418967fa.accept_16_1_5_15_1_2918 81 165 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 165 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 165 287 (accept_3_2 79 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 165 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 165 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 165 287 (accept_3_2 76 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 165 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 165 287 (accept_3_2 73 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 165 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 165 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 71 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 287 (accept_3_2 70 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 165 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 165 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 165 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 165 287 (accept_3_2 67 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 165 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 165 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 165 287 (accept_3_2 64 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 165 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 165 287 (accept_3_2 61 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 165 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 165 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 287 (accept_3_2 58 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 165 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 57 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 165 287 (accept_3_2 55 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 165 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 165 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 53 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 287 (accept_3_2 52 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 165 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 165 287 (accept_3_2 49 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 165 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 165 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 287 (accept_3_2 46 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 287 (accept_3_2 43 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 165 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 165 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 287 (accept_3_2 40 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 287 (accept_3_2 37 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 165 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 165 287 (Polychromatic418967fa.accept_17_1_12_15_1_1263 35 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 287 (accept_3_2 34 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 165 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 287 (accept_3_2 31 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 165 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 165 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 287 (accept_3_2 28 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 287 (accept_3_2 25 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 165 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 165 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 287 (accept_3_2 22 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 165 287 (accept_3_2 19 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 165 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 165 287 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 287 (accept_3_2 16 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 165 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 287 (accept_3_2 13 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 165 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 165 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 287 (accept_3_2 10 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 287 (Polychromatic418967fa.accept_20_9_5_7_1_6336 9 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 287 (accept_3_2 7 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  165 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 165 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 287 (accept_3_2 4 165 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 165 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 287 (accept_3_2 1 165 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 124 164 287 (Eq.refl Bool.true) (allA_succ_of_gcd 123 164 287 41 3 4 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 122 164 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 122 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 164 287 (accept_3_2 121 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 164 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 120 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 164 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 119 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 164 287 (accept_3_2 118 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 117 164
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 164 287
  (Polychromatic418967fa.accept_13_12_8_1_1_825 116 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 164 287 (accept_3_2 115 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 164 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 114 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 164 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 113 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 164 287 (accept_3_2 112 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 111 164
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 164 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 110 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 164 287 (accept_3_2 109 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 164 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 108 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 164 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 107 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 164 287 (accept_3_2 106 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 164
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 164 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 104 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 164 287 (accept_3_2 103 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 164 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 164 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 101 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 164 287 (accept_3_2 100 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 164 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 164 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 98 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 164 287 (accept_3_2 97 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 164 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 164 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 164 287 (accept_3_2 94 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 164 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 92 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 164 287 (accept_3_2 91 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 164 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 164 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 89 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 164 287 (accept_3_2 88 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 164 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 164 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 164 287 (accept_3_2 85 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 164 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 164 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 164 287 41 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 81
  164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 164 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 80 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 164 287 (accept_3_2 79 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 164 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 164 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 164 287 (accept_3_2 76 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 164 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 164 287 (accept_3_2 73 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 164 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 164 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 71 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 164 287 (accept_3_2 70 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 164 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 164 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 164 287 (accept_3_2 67 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 164 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 164 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 164 287 (accept_3_2 64 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 164 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 164 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 62 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 164 287 (accept_3_2 61 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 164 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 164 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 164 287 (accept_3_2 58 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 164 287
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 56 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 164 287 (accept_3_2 55 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 164 287 (Polychromatic418967fa.accept_23_8_3_11_1_14511 54 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 164 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 53 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 164 287 (accept_3_2 52 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 164 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 164 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 164 287 (accept_3_2 49 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 164 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 164 287 (Polychromatic418967fa.accept_17_13_11_15_1_5556 47 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 164 287 (accept_3_2 46 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 164 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 164 287
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 164 287 (accept_3_2 43 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 164 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 41 164 287 41 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 40 164 287 (accept_3_2 40 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 164 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 164 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 164
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 164 287 (accept_3_2 37 164
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 164 287
  (Polychromatic418967fa.accept_19_17_12_2_1_6880 36 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 164 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 164 287 (accept_3_2 34 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 164 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 164 287 (accept_3_2 31 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 164 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 164 287 (Polychromatic418967fa.accept_18_11_2_17_1_3490 29 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 164 287 (accept_3_2 28 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 164 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 164 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 164 287 (accept_3_2 25 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 164 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 164 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 164 287 (accept_3_2 22 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 164 287
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 164 287 (accept_3_2 19 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 164 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 164 287 (Polychromatic418967fa.accept_14_3_10_7_1_3773 17 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 287 (accept_3_2 16 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 164 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 164 287 (accept_3_2 13 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 164 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 164 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 287 (accept_3_2 10 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 287
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 287 (accept_3_2 7 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 287 (accept_3_2 4 164 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 287 (accept_3_2 1 164 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 163 287 (Eq.refl Bool.true) (allA_of_3_0 125 163 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 126 162 287 (Eq.refl Bool.true) (allA_succ_of_accept 125 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  125 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 162 287 (accept_3_2
  124 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 162 287
  (Polychromatic418967fa.accept_15_3_12_2_1_507 123 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 162 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 122 162 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 162 287 (accept_3_2 121 162 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 162 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 120 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 162 287
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 119 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 162 287 (accept_3_2 118 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 162 287 (Polychromatic418967fa.accept_26_12_6_1_1_17640 116 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 162 287 (accept_3_2 115 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 162 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 114 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 162 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 162 287 (accept_3_2 112 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 162 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 111 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 162 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 110 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 162 287 (accept_3_2 109 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 162 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 108 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 162 287
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 107 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 162 287 (accept_3_2 106 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 162 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 104 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 162 287 (accept_3_2 103 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 162 287 (Polychromatic418967fa.accept_21_18_15_14_1_8871 102
  162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 162 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 162 287 (accept_3_2 100 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 162 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 99 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 162 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 98 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 162 287 (accept_3_2 97 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 162 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 96 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 162 287
  (Polychromatic418967fa.accept_10_5_2_7_1_345 95 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 162 287 (accept_3_2 94 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 162 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 92 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 162 287 (accept_3_2 91 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 162 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 90 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 162 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 162 287 (accept_3_2 88 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 162 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 87 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 162 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 86 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 162 287 (accept_3_2 85 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 162 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 84 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 162 287
  (Polychromatic418967fa.accept_13_5_6_1_1_822 83 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 162 287 (accept_3_2 82 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 162 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 80 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 162 287 (accept_3_2 79 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 162 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 78 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 162 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 162 287 (accept_3_2 76 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 162 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 75 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 162 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 74 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 162 287 (accept_3_2 73 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 162 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 72 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 162 287
  (Polychromatic418967fa.accept_14_1_8_7_1_1253 71 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 162 287 (accept_3_2 70 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 162 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 68 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 162 287 (accept_3_2 67 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 162 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 66 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 162 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 162 287 (accept_3_2 64 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 162 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 162 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 62 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 162 287 (accept_3_2 61 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 162 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 162 287
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 59 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 162 287 (accept_3_2 58 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 162 287 (Polychromatic418967fa.accept_19_18_10_2_1_2850 56 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 162 287 (accept_3_2 55 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 162 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 162 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 162 287 (accept_3_2 52 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 162 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 162 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 50 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 287 (accept_3_2 49 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 162 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 162 287
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 47 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 162 287 (accept_3_2 46 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 162 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 287 (accept_3_2 43 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 162 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 162 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 162 287 (accept_3_2 40 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 162 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 162 287 (Polychromatic418967fa.accept_20_18_2_7_1_6285 38 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 287 (accept_3_2 37 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 162 287
  (Polychromatic418967fa.accept_10_5_2_7_1_345 35 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 162 287 (accept_3_2 34 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 162 287 (Polychromatic418967fa.accept_19_13_10_2_1_12473 32 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 287 (accept_3_2 31 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 287 (Polychromatic418967fa.accept_19_11_10_2_1_9757 30 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 162 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 162 287 (accept_3_2 28 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 162 287 (Polychromatic418967fa.accept_14_13_8_7_1_1224 27 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 162 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 287 (accept_3_2 25 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 162 287
  (Polychromatic418967fa.accept_17_6_9_15_1_3185 23 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 162 287 (accept_3_2 22 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 162 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 20 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 287 (accept_3_2 19 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 162 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 287 (accept_3_2 16 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 162 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 162 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 287 (accept_3_2 13 162 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 287 (Polychromatic418967fa.accept_16_12_2_15_1_490 12 162
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 162 287
  (Polychromatic418967fa.accept_19_11_10_2_1_9757 11 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 162 287 (accept_3_2 10 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 162 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 162 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 287 (accept_3_2 7 162 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 6
  162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 287 (accept_3_2 4 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  162 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 162 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 162 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 162 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 287 (accept_3_2 1 162 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 162
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 127 161 287 (Eq.refl Bool.true) (allA_succ_of_gcd 126 161 287 7 18 23 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 161 287
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 125 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 161 287 (accept_3_2 124 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 161 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 123 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 161 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 122 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 161 287 (accept_3_2 121 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 161 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 120 161
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 119 161 287 7 17 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 118 161 287 (accept_3_2
  118 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 161 287
  (Polychromatic418967fa.accept_16_5_1_15_1_3922 117 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 161 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 116 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 161 287 (accept_3_2 115 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 161 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 161
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 161 287
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 113 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 161 287 7 16 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 161 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 111 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 161 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 161 287 (accept_3_2 109 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 161 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 108 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 161 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 107 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 161 287 (accept_3_2 106 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 105 161 287 7 15 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 161 287 (Polychromatic418967fa.accept_10_4_1_7_1_371
  104 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 161 287 (accept_3_2
  103 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 161 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 161 287 (Polychromatic418967fa.accept_16_5_1_15_1_3922 101 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 161 287 (accept_3_2 100 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 161 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 99 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 161 287 7 14 23 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 161 287 (accept_3_2 97 161 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 161 287 (Polychromatic418967fa.accept_10_6_1_7_1_342
  96 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 161 287
  (Polychromatic418967fa.accept_13_4_5_1_1_833 95 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 161 287 (accept_3_2 94 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 161 287 (Polychromatic418967fa.accept_19_17_9_2_1_12492 93 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 161 287 (Polychromatic418967fa.accept_22_4_7_1_1_13138 92 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 161 287 7 13 23 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 161 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 161 287 (Polychromatic418967fa.accept_25_14_11_12_1_16013 89 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 161 287 (accept_3_2 88 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 161 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 87 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 161 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 161 287 (accept_3_2 85 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84
  161 287 7 12 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 161 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 83 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 161 287 (accept_3_2 82 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 161 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 81 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 161 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 80 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 161 287 (accept_3_2 79 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 161 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 77 161 287 7 11 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 161 287 (accept_3_2 76 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 161 287 (Polychromatic418967fa.accept_16_11_1_15_1_1123 75 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 161 287 (accept_3_2 73
  161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 161 287
  (Polychromatic418967fa.accept_11_6_7_1_1_564 72 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 161 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 71 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 161 287 7 10 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 161 287 (Polychromatic418967fa.accept_13_4_5_1_1_833
  69 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 287
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 68 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 161 287 (accept_3_2 67 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 287 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 287 (accept_3_2 64 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 161 287 7 9 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 161 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62
  161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 161 287 (accept_3_2 61
  161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 161 287
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 60 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 161 287 (Polychromatic418967fa.accept_16_11_1_15_1_1123 59 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 287 (accept_3_2 58 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 287 (Polychromatic418967fa.accept_17_6_8_15_1_10655 57 161 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 161 287 7 8 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 161 287 (accept_3_2 55
  161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 161 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 161 287 (Polychromatic418967fa.accept_16_5_1_15_1_3922 53 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 287 (accept_3_2 52 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 161 287 (Polychromatic418967fa.accept_13_12_5_1_1_1383 51 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 161 287 7 7 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 161 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 47 161
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 287 (accept_3_2 46 161
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 287
  (Polychromatic418967fa.accept_13_6_5_1_1_834 45 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 161 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 44 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 287 (accept_3_2 43 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 161 287 7 6 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 161 287 (Polychromatic418967fa.accept_27_14_26_17_1_17639 41 161 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 287 (accept_3_2 40 161 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 287 (Polychromatic418967fa.accept_11_6_7_1_1_564
  39 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 287 (accept_3_2 37 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 161 287 7 5 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 161 287 (accept_3_2 34 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 161 287 (Polychromatic418967fa.accept_22_11_7_1_1_13135 33 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 287 (Polychromatic418967fa.accept_13_6_5_1_1_834
  32 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 287 (accept_3_2 31
  161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 161 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 161 287 7 4 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 161 287
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 287 (accept_3_2 25 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 287
  (Polychromatic418967fa.accept_17_6_8_15_1_10655 23 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 161 287 (accept_3_2 22 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 161 287 7 3 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 161 287 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 287 (accept_3_2 19 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 161 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 287 (Polychromatic418967fa.accept_11_6_7_1_1_564
  17 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 287 (accept_3_2 16
  161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 287
  (Polychromatic418967fa.accept_19_15_9_2_1_8347 15 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 161 287 7 2 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 161 287 (accept_3_2 13 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 287 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 287 (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 287 (accept_3_2 10 161 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 161 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 287
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 161 287 7 1 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 161 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 287 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 161
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 287 (accept_3_2 4 161 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144
  3 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 287 (accept_3_2 1 161 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 160 287 (Eq.refl Bool.true) (allA_of_3_0 128 160 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 129 159 287 (Eq.refl Bool.true) (allA_succ_of_accept 128 159 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 128 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 159 287 (accept_3_2 127 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  126 159 287 (Polychromatic418967fa.accept_20_6_19_7_1_3375 126 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 125 159 287 (Polychromatic418967fa.accept_22_15_5_1_1_8441 125 159 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 159 287 (accept_3_2 124 159 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 159 287
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 123 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 122 159 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 159 287 (accept_3_2 121 159 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 120 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 159 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 119 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 159 287 (accept_3_2 118 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 159 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 117 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 116 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 159 287 (accept_3_2 115 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 159 287 (Polychromatic418967fa.accept_14_2_5_7_1_3767 114 159
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 159 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 113 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 159 287 (accept_3_2 112 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 111 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 159 287 (accept_3_2 109 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 159 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 108 159
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 159 287
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 107 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 159 287 (accept_3_2 106 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 159 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 105 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 159 287 (accept_3_2 103 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 159
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 159 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 159 287 (accept_3_2 100 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 159 287 (Polychromatic418967fa.accept_17_14_6_15_1_3151 99 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 159 287 (accept_3_2 97 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 159 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 96 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 159 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 159 287 (accept_3_2 94 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 287 (accept_3_2 91 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 159 287 (Polychromatic418967fa.accept_19_14_7_2_1_11116 90 159 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 159 287
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 89 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 159 287 (accept_3_2 88 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 159 287 (Polychromatic418967fa.accept_21_3_12_14_1_8848 87 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 287 (accept_3_2 85 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 159 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 159 287 (accept_3_2 82 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 159 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 287 (accept_3_2 79 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 159 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 78 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 159 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 159 287 (accept_3_2 76 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 287 (accept_3_2 73 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 159 287
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 71 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 159 287 (accept_3_2 70 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 159 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 287 (accept_3_2 67 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 159 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 159 287 (accept_3_2 64 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 159 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 287 (accept_3_2 61 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 287 (Polychromatic418967fa.accept_17_9_6_15_1_5454 60 159 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 159 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 159 287 (accept_3_2 58 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 287 (accept_3_2 55 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 287
  (Polychromatic418967fa.accept_15_8_9_2_1_1897 53 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 287 (accept_3_2 52 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 159 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 51 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 287 (accept_3_2 49 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 159 287 (accept_3_2 46 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 159 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 287 (accept_3_2 43 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 42 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 287 (accept_3_2 40 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 287 (accept_3_2 37 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 287 (Polychromatic418967fa.accept_19_17_7_2_1_11110 36 159 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 287
  (Polychromatic418967fa.accept_19_16_7_2_1_12512 35 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 159 287 (accept_3_2 34 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 159 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 159 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 159 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 287 (accept_3_2 31 159 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308
  30 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 287 (accept_3_2 28 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 287 (Polychromatic418967fa.accept_18_9_15_17_1_3497 27 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 287 (accept_3_2 25 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 287 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 159 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 287 (accept_3_2 22 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 287 (accept_3_2 19 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 287 (accept_3_2 16 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 15 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 287 (accept_3_2 13 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 287 (accept_3_2 10 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 287 (accept_3_2 7 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 159 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 287 (accept_3_2 4 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 159 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 287 (accept_3_2 1 159 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 130 158 287 (Eq.refl Bool.true) (allA_succ_of_accept 129 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  129 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 158 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 128 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 158 287 (accept_3_2 127 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  126 158 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 126 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 125 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 125 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 158 287 (accept_3_2 124 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 123 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 123 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 158 287
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 122 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 158 287 (accept_3_2 121 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 158 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 120 158 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 158 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 119 158
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 158 287 (accept_3_2 118 158
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 158 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 117 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 158 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 116 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 158 287 (accept_3_2 115 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 158 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 114 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 158 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 158 287 (accept_3_2 112 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 111 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 158 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 158 287 (accept_3_2 109 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 158 287 (Polychromatic418967fa.accept_14_10_4_7_1_1214 108
  158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 158 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 107 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 158 287 (accept_3_2 106 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 158 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 104 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 158 287 (accept_3_2 103 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 158 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 158
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 158 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 158 287 (accept_3_2 100 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 158 287 (Polychromatic418967fa.accept_17_13_5_15_1_8103 98 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 158 287 (accept_3_2 97 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 158 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 158 287
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 95 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 158 287 (accept_3_2 94 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 158 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 158 287 (accept_3_2 91 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 158 287 (Polychromatic418967fa.accept_13_12_2_1_1_2909 90 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 158 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 158 287 (accept_3_2 88 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 158 287 (Polychromatic418967fa.accept_19_10_6_2_1_6907 86 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 158 287 (accept_3_2 85 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 158 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 158 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 158 287 (accept_3_2 82 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 158 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 80 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 158 287 (accept_3_2 79 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 158 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 158 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 158 287 (accept_3_2 76 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 158 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 158 287 (accept_3_2 73 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 158 287 (Polychromatic418967fa.accept_19_15_6_2_1_6865 72 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 158 287
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 71 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 158 287 (accept_3_2 70 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 158 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 68 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 158 287 (accept_3_2 67 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 158 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 158 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 158 287 (accept_3_2 64 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 158 287 (Polychromatic418967fa.accept_17_11_5_15_1_8144 62 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 158 287 (accept_3_2 61 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 158 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 158 287
  (Polychromatic418967fa.accept_10_9_8_7_1_714 59 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 158 287 (accept_3_2 58 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 158 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 158 287 (accept_3_2 55 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 158 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 158 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 158 287 (accept_3_2 52 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 158 287 (Polychromatic418967fa.accept_19_12_6_2_1_5424 50 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 158 287 (accept_3_2 49 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 158 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 158 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 158 287 (accept_3_2 46 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 158 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 158 287 (accept_3_2 43 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 158 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 158 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 158 287 (accept_3_2 40 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 158 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 158 287 (accept_3_2 37 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 158 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 158 287
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 158 287 (accept_3_2 34 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 158 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 32 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 158 287 (accept_3_2 31 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 158 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 158 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 158 287 (accept_3_2 28 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 158 287 (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 158 287 (accept_3_2 25 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 158 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 158 287
  (Polychromatic418967fa.accept_16_7_14_15_1_2932 23 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 158 287 (accept_3_2 22 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 287 (accept_3_2 19 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 158 287
  (Polychromatic418967fa.accept_21_18_11_14_1_8846 18 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 287 (accept_3_2 16 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 287
  (Polychromatic418967fa.accept_23_14_20_11_1_17638 14 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 158 287 (accept_3_2 13 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 158 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 158 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 287 (accept_3_2 10 158 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 287 (accept_3_2 7 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 287 (accept_3_2 4 158 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 158 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 287 (accept_3_2 1 158 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 131 157 287 (Eq.refl Bool.true) (allA_of_3_0 131 157 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 132 156 287 (Eq.refl Bool.true) (allA_succ_of_accept 131 156 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 131 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 156 287 (accept_3_2 130 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 156 287 (Polychromatic418967fa.accept_20_9_16_7_1_1129 129 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 128 156 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 128 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 156 287 (accept_3_2 127 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 156 287 (Polychromatic418967fa.accept_19_12_4_2_1_4121 126
  156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 156 287
  (Polychromatic418967fa.accept_16_13_12_15_1_6290 125 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 156 287 (accept_3_2 124 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 156 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 123 156 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 156 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 122 156
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 156 287 (accept_3_2 121 156
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 156 287
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 120 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 156 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 119 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 156 287 (accept_3_2 118 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 156 287 (Polychromatic418967fa.accept_14_5_2_7_1_2804 117 156
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 156 287
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 116 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 156 287 (accept_3_2 115 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 114 156 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 156 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 113 156
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 156 287 (accept_3_2 112 156
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 156 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 111 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 156 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 110 156 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 156 287 (accept_3_2 109 156 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 156 287 (Polychromatic418967fa.accept_21_3_9_14_1_5701 108 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 156 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 107 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 156 287 (accept_3_2 106 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 156 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 104 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 156 287 (accept_3_2 103 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 156 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 102 156
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 156 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 101 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 156 287 (accept_3_2 100 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 156 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 99 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 156 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 98 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 156 287 (accept_3_2 97 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 156 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 95 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 156 287 (accept_3_2 94 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 156 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 93 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 156 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 92 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 156 287 (accept_3_2 91 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 156 287 (Polychromatic418967fa.accept_19_14_4_2_1_2840 90 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 156 287
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 89 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 156 287 (accept_3_2 88 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 156 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 86 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 156 287 (accept_3_2 85 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 156 287 (Polychromatic418967fa.accept_16_4_12_15_1_6289 84 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 156 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 83 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 156 287 (accept_3_2 82 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 156 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 81 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 156 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 80 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 156 287 (accept_3_2 79 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 156 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 156 287 (accept_3_2 76 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 156 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 156 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 156 287 (accept_3_2 73 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 156 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 72 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 156 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 71 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 156 287 (accept_3_2 70 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 156 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 156 287 (accept_3_2 67 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 156 287 (Polychromatic418967fa.accept_16_2_12_15_1_2908 66 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 156 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 156 287 (accept_3_2 64 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 156 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 156 287 (Polychromatic418967fa.accept_19_5_4_2_1_6840 62 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 287 (accept_3_2 61 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 156 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 156 287 (accept_3_2 58 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 156 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 57 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 156 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 287 (accept_3_2 55 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 156 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 156 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 53 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 156 287 (accept_3_2 52 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 156 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 156 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 287 (accept_3_2 49 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 287 (Polychromatic418967fa.accept_17_14_3_15_1_5449 48 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 156 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 156 287 (accept_3_2 46 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 156 287 (Polychromatic418967fa.accept_16_13_12_15_1_6290 45 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 287 (Polychromatic418967fa.accept_19_6_4_2_1_1726 44 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 287 (accept_3_2 43 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 156 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 156 287 (accept_3_2 40 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 156 287 (Polychromatic418967fa.accept_21_18_9_14_1_8832 39 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 156 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 287 (accept_3_2 37 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 156 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 156 287 (accept_3_2 34 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 156 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 287 (accept_3_2 31 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 287 (Polychromatic418967fa.accept_19_11_4_2_1_1700 30 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 156 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 156 287 (accept_3_2 28 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 156 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 156 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 287 (accept_3_2 25 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 156 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 156 287 (accept_3_2 22 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 156 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 156 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 287 (accept_3_2 19 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 287 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 156 287
  (Polychromatic418967fa.accept_19_17_4_2_1_8360 17 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 156 287 (accept_3_2 16 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 156 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 287 (accept_3_2 13 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 156 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 156 287 (accept_3_2 10 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  156 287 (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 156 287 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 287 (accept_3_2 7 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 156 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 156 287 (accept_3_2 4 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  156 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 156 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 156 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 287 (accept_3_2 1 156 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 156
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 133 155 287 (Eq.refl Bool.true) (allA_succ_of_accept 132 155 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 132 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 155 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 131 155 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 155 287 (accept_3_2 130 155 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 129 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 155 287
  (Polychromatic418967fa.accept_10_8_5_7_1_358 128 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 155 287 (accept_3_2 127 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  126 155 287 (Polychromatic418967fa.accept_17_7_2_15_1_1255 126 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 125 155 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 125 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 155 287 (accept_3_2 124 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592
  123 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 155 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 122 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 155 287 (accept_3_2 121 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 120 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 155 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 119 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 155 287 (accept_3_2 118 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 155 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 117
  155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 155 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 116 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 155 287 (accept_3_2 115 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 114 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 155 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 113 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 155 287 (accept_3_2 112 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 111 155
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 155 287
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 110 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 155 287 (accept_3_2 109 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 155 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 108 155 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 155 287 (Polychromatic418967fa.accept_19_12_3_2_1_12509 107
  155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 155 287 (accept_3_2 106
  155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 155 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 105 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 155 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 155 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 155 287 (accept_3_2 103 155 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 155 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 101 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 155 287 (accept_3_2 100 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 155 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 99 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 155 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 98 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 155 287 (accept_3_2 97 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 155 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 155 287 (accept_3_2 94 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 155 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 92 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 155 287 (accept_3_2 91 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 155 287 (Polychromatic418967fa.accept_14_6_1_7_1_2775 90 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 155 287
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 89 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 155 287 (accept_3_2 88 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 155 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 155 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 86 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 155 287 (accept_3_2 85 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 155 287 (Polychromatic418967fa.accept_8_4_3_7_1_491
  84 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 155 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 83 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 155 287 (accept_3_2 82 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 155 287 (Polychromatic418967fa.accept_16_1_11_15_1_498 81 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 155 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 80 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 155 287 (accept_3_2 79 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 155 287 (accept_3_2 76 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 155 287 (Polychromatic418967fa.accept_15_14_5_2_1_4761 74 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 155 287 (accept_3_2 73 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 155 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 155
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 71 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 155 287 (accept_3_2 70 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 155 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 287 (accept_3_2 67 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 287
  (Polychromatic418967fa.accept_16_1_11_15_1_498 65 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 155 287 (accept_3_2 64 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 155 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 155 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 62 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 287 (accept_3_2 61 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 287 (accept_3_2 58 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 287 (accept_3_2 55 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 54 155
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 53 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 287 (accept_3_2 52 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 287 (accept_3_2 49 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 287
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 287 (accept_3_2 46 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 287 (Polychromatic418967fa.accept_20_5_15_7_1_7869 45 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 287 (accept_3_2 43 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 287 (accept_3_2 40 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 38 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 287 (accept_3_2 37 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 287
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 35 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 155 287 (accept_3_2 34 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 155 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 287 (accept_3_2 31 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108
  30 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 287 (accept_3_2 28 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 287 (accept_3_2 25 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 287 (accept_3_2 22 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 287 (accept_3_2 19 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 287
  (Polychromatic418967fa.accept_16_1_11_15_1_498 17 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 287 (accept_3_2 16 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 287 (accept_3_2 13 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 155 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 287
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 155 287 (accept_3_2 10 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 155 287 (Polychromatic418967fa.accept_25_9_5_12_1_17637 9 155 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 287 (accept_3_2 7 155 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 287 (accept_3_2 4 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 155 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 287 (accept_3_2 1 155 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 134 154 287 (Eq.refl Bool.true) (allA_of_3_0 134 154 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 135 153 287 (Eq.refl Bool.true) (allA_succ_of_accept 134 153 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 134 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 153 287 (accept_3_2 133 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  132 153 287 (Polychromatic418967fa.accept_14_6_13_7_1_2015 132 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 131 153 287 (Polychromatic418967fa.accept_27_23_18_17_1_12038 131 153 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 153 287 (accept_3_2 130 153 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 153 287
  (Polychromatic418967fa.accept_19_15_1_2_1_6894 129 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 153 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 128 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 153 287 (accept_3_2 127 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 126 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 153 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 125 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 153 287 (accept_3_2 124 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 153 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 123 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 122 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 122 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 153 287 (accept_3_2 121 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 153 287 (Polychromatic418967fa.accept_14_8_13_7_1_2798 120
  153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 153 287
  (Polychromatic418967fa.accept_11_9_10_1_1_581 119 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 153 287 (accept_3_2 118 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 153 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 117 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 116 153 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 153 287 (accept_3_2 115 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 153 287
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 113 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 153 287 (accept_3_2 112 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 153 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 111 153 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27
  110 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 153 287 (accept_3_2
  109 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 153 287
  (Polychromatic418967fa.accept_11_9_10_1_1_581 108 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 153 287 (Polychromatic418967fa.accept_19_12_1_2_1_9750 107 153 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 153 287 (accept_3_2 106 153 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 153 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 105 153 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 153 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 104 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 153 287 (accept_3_2 103 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 153 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 101 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 287 (accept_3_2 100 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 153 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 153 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 153 287 (accept_3_2 97 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 153 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 96 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 153 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 95 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 153 287 (accept_3_2 94 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 153 287 (Polychromatic418967fa.accept_21_9_6_14_1_7228 93 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 153 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 153 287 (accept_3_2 91 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 153 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 89 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 153 287 (accept_3_2 88 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 153 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 87 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 153 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 153 287 (accept_3_2 85 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 153 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 84 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 153 287 (Polychromatic418967fa.accept_19_7_1_2_1_9792 83 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 287 (accept_3_2 82 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 153 287 (Polychromatic418967fa.accept_21_18_6_14_1_2812 81 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 153 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 153 287 (accept_3_2 79 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 153 287 (Polychromatic418967fa.accept_22_11_21_1_1_13183 77 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 287 (accept_3_2 76 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 75 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 153 287 (accept_3_2 73 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 153 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 72 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 153 287 (Polychromatic418967fa.accept_14_1_13_7_1_1205 71 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 287 (accept_3_2 70 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 69 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 153 287 (accept_3_2 67 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 153 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 287 (accept_3_2 64 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 287 (accept_3_2 61 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 153 287 (Polychromatic418967fa.accept_19_3_1_2_1_6860 60 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 287 (Polychromatic418967fa.accept_15_14_3_2_1_2811 59 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 287 (accept_3_2 58 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 287 (accept_3_2 55 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 287 (accept_3_2 52 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 287 (accept_3_2 49 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 153 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 48 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 287 (Polychromatic418967fa.accept_19_9_1_2_1_6839 47 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 287 (accept_3_2 46 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 287 (accept_3_2 43 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 153 287 (Polychromatic418967fa.accept_19_3_1_2_1_6860 41 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 287 (accept_3_2 40 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 153 287 (accept_3_2 37 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 153 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 153 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 287 (accept_3_2 34 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 287 (Polychromatic418967fa.accept_18_15_9_17_1_6043 33 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 287 (accept_3_2 31 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 153 287 (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 287 (accept_3_2 28 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 287 (accept_3_2 25 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 153 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 287 (Polychromatic418967fa.accept_21_2_6_14_1_1569 23 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 287 (accept_3_2 22 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 287 (Polychromatic418967fa.accept_27_21_18_17_1_15891 21
  153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 287 (accept_3_2 19 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 153 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 287 (accept_3_2 16 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 153
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 287 (accept_3_2 13 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 287 (accept_3_2 10 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 153 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 287 (accept_3_2 7 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 153 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 287 (accept_3_2 4 153 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 153 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 287 (accept_3_2 1 153 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 136 152 287 (Eq.refl Bool.true) (allA_succ_of_accept 135 152 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 135 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 152 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 134 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 152 287 (accept_3_2 133 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 152 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 132 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 152 287
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 131 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 130 152 287 (accept_3_2 130 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 129 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 129 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 152 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 128
  152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 152 287 (accept_3_2 127
  152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 152 287
  (Polychromatic418967fa.accept_20_6_12_7_1_12130 126 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 125 152 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 125 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 152 287 (accept_3_2 124 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 123 152
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 152 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 122 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 152 287 (accept_3_2 121 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 152 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 120 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 119 152 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 119 152 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 152 287 (accept_3_2 118 152 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32
  117 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 152 287
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 116 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 152 287 (accept_3_2 115 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 152 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 114 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 152 287 (Polychromatic418967fa.accept_16_1_8_15_1_1945 113
  152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 152 287 (accept_3_2 112
  152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 152 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 152 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 110 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 152 287 (accept_3_2 109 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 152 287 (Polychromatic418967fa.accept_16_12_8_15_1_5119 108 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 152 287
  (Polychromatic418967fa.accept_14_9_12_7_1_597 107 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 152 287 (accept_3_2 106 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 152 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 104 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 152 287 (accept_3_2 103 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 152 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 102
  152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 152 287
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 101 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 152 287 (accept_3_2 100 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 152 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 98 152
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 152 287 (accept_3_2 97 152
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 152 287
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 96 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 152 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 95 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 152 287 (accept_3_2 94 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 152 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 152 287
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 92 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 152 287 (accept_3_2 91 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 152 287 (Polychromatic418967fa.accept_24_18_8_23_1_14280 90 152 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 152 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096
  89 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 152 287 (accept_3_2 88
  152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 152 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 87 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 152 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 86 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 152 287 (accept_3_2 85 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 152 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 84 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 152 287
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 83 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 152 287 (accept_3_2 82 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 152 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 80 152 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 152 287 (accept_3_2 79 152 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 152 287 (Polychromatic418967fa.accept_21_15_5_14_1_11856 78 152 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 152 287
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 77 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 152 287 (accept_3_2 76 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 152 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 74 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 152 287 (accept_3_2 73 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 152 287 (Polychromatic418967fa.accept_14_2_12_7_1_617 72 152
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 152 287
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 71 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 152 287 (accept_3_2 70 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 152 287 (Polychromatic418967fa.accept_16_4_8_15_1_1113 68 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 152 287 (accept_3_2 67 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 152 287 (Polychromatic418967fa.accept_20_6_12_7_1_12130 66 152
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 152 287
  (Polychromatic418967fa.accept_10_5_2_7_1_345 65 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 152 287 (accept_3_2 64 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 152 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 62 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 152 287 (accept_3_2 61 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 152 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 152
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 152 287
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 59 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 152 287 (accept_3_2 58 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 152 287 (Polychromatic418967fa.accept_18_2_8_17_1_4754 56 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 152 287 (accept_3_2 55 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 152 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 152
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 152 287
  (Polychromatic418967fa.accept_21_11_5_14_1_4142 53 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 152 287 (accept_3_2 52 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 152 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 152 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 152
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 152 287 (accept_3_2 49 152
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 152 287
  (Polychromatic418967fa.accept_17_14_16_15_1_5509 48 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 152 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147 47 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 152 287 (accept_3_2 46 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 152 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 152 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 152 287 (accept_3_2 43 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 152 287 (Polychromatic418967fa.accept_20_2_12_7_1_4799 42 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 152 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 41 152 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 287 (accept_3_2 40 152 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 152 287 (accept_3_2 37 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 152 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 152 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 287 (accept_3_2 34 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 152 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 287
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 152 287 (accept_3_2 31 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 152 287 (Polychromatic418967fa.accept_14_2_12_7_1_617 30 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 152 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 29 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 287 (accept_3_2 28 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 152 287 (accept_3_2 25 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 152 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 152 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 287 (accept_3_2 22 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 287
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 20 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 152 287 (accept_3_2 19 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 152 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 152 287 (Polychromatic418967fa.accept_16_1_8_15_1_1945 17 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 287 (accept_3_2 16 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 287
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 287 (accept_3_2 13 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 287 (Polychromatic418967fa.accept_16_12_8_15_1_5119 12 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 287 (accept_3_2 10 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 287
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 287 (accept_3_2 7 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 152 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 287 (accept_3_2 4 152 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 287 (accept_3_2 1 152 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 137 151 287 (Eq.refl Bool.true) (allA_of_3_0 137 151 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 138 150 287 (Eq.refl Bool.true) (allA_succ_of_accept 137 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  137 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 150 287 (accept_3_2
  136 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 150 287
  (Polychromatic418967fa.accept_16_7_6_15_1_495 135 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 150 287 (Polychromatic418967fa.accept_21_8_3_14_1_4165 134 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 150 287 (accept_3_2 133 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 132 150 287 (Polychromatic418967fa.accept_21_6_3_14_1_11869 132 150 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 150 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 131 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 150 287 (accept_3_2 130 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 129 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 150 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 128 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 150 287 (accept_3_2 127 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 150 287 (Polychromatic418967fa.accept_19_12_17_2_1_6888 126
  150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 125 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 150 287 (accept_3_2 124 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 150 287 (Polychromatic418967fa.accept_13_6_7_1_1_335 123 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 150 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 122 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 150 287 (accept_3_2 121 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 120 150
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 150 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 119 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 150 287 (accept_3_2 118 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 150 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 116 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 150 287 (accept_3_2 115 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 150 287 (Polychromatic418967fa.accept_17_12_14_15_1_5561 114
  150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 150 287 (accept_3_2 112 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 111 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 150 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 110 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 150 287 (accept_3_2 109 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 150 287 (Polychromatic418967fa.accept_17_6_14_15_1_5505 108
  150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 150 287
  (Polychromatic418967fa.accept_13_3_7_1_1_334 107 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 150 287 (accept_3_2 106 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 150 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 104 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 150 287 (accept_3_2 103 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 150
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 150 287 (accept_3_2 100 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 150 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 99 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 150 287 (Polychromatic418967fa.accept_19_3_17_2_1_6963 98 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 150 287 (accept_3_2 97 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 150 287 (Polychromatic418967fa.accept_21_12_3_14_1_10498 96
  150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 150 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 150 287 (accept_3_2 94 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 150 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 92 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 150 287 (accept_3_2 91 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 150 287 (Polychromatic418967fa.accept_19_14_17_2_1_1720 90 150 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 150 287 (accept_3_2 88 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 150 287 (Polychromatic418967fa.accept_14_3_10_7_1_3773 87 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 150 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 150 287 (accept_3_2 85 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 150 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 150 287 (accept_3_2 82 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 150 287 (Polychromatic418967fa.accept_17_12_14_15_1_5561 80 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 150 287 (accept_3_2 79 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 150 287 (Polychromatic418967fa.accept_20_18_10_7_1_9245 78 150
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 150 287 (accept_3_2 76 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 150 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 150 287 (accept_3_2 73 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 150 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 72 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 150 287
  (Polychromatic418967fa.accept_13_6_7_1_1_335 71 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 150 287 (accept_3_2 70 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 150 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 150 287 (accept_3_2 67 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 150 287 (accept_3_2 64 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 150 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 150 287 (Polychromatic418967fa.accept_19_5_17_2_1_11164 62 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 150 287 (accept_3_2 61 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 150 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 60 150
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 150 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 150 287 (accept_3_2 58 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 150 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 150 287 (accept_3_2 55 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 150 287 (Polychromatic418967fa.accept_17_3_14_15_1_5502 54 150 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 150 287 (accept_3_2 52 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 150 287 (Polychromatic418967fa.accept_18_15_6_17_1_2386 51 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 150 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 150 287 (accept_3_2 49 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 150 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 150 287 (accept_3_2 46 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 150 287 (Polychromatic418967fa.accept_21_2_3_14_1_5690 44 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 287 (accept_3_2 43 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 150 287 (Polychromatic418967fa.accept_13_3_7_1_1_334 42 150
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 150 287 (accept_3_2 40 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 150 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 287 (accept_3_2 37 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 150 287 (Polychromatic418967fa.accept_21_15_3_14_1_4141 36 150 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 150 287
  (Polychromatic418967fa.accept_19_16_17_2_1_6856 35 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 150 287 (accept_3_2 34 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 150 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 287 (accept_3_2 31 150 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308
  30 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 150 287 (accept_3_2 28 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 150 287 (Polychromatic418967fa.accept_21_6_3_14_1_11869 27 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 150 287 (Polychromatic418967fa.accept_19_7_17_2_1_6855 26 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 287 (accept_3_2 25 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 150
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 150 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 287 (accept_3_2 22 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 150 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 287 (accept_3_2 19 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 287 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 150 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 150 287 (accept_3_2 16 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 150 287 (Polychromatic418967fa.accept_18_15_6_17_1_2386 15 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 150 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 287 (accept_3_2 13 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 150 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 150 287 (accept_3_2 10 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  150 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 150 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 287 (accept_3_2 7 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 150 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 150 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 150 287 (accept_3_2 4 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  150 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 150 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 150 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 287 (accept_3_2 1 150 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 150
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 139 149 287 (Eq.refl Bool.true) (allA_succ_of_accept 138 149 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 138 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 137 149 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 137 149 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 149 287 (accept_3_2 136 149 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 135 149 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 135 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 149 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 134 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 149 287 (accept_3_2 133 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  132 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 132 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 131 149 287 (Polychromatic418967fa.accept_14_5_9_7_1_590 131 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 149 287 (accept_3_2 130 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 129 149
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 149 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 128 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 149 287 (accept_3_2 127 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  126 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 126 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 125 149 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 125 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 149 287 (accept_3_2 124 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 123 149
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 149 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 122 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 149 287 (accept_3_2 121 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 120 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 149 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 119 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 149 287 (accept_3_2 118 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 149 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 117 149
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 149 287
  (Polychromatic418967fa.accept_16_4_5_15_1_5083 116 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 149 287 (accept_3_2 115 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 149 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 149 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 113 149
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 149 287 (accept_3_2 112 149
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 149 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 111 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 149 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 149 287 (accept_3_2 109 149 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 149 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 108 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 149 287
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 107 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 149 287 (accept_3_2 106 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 105 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 149 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 104 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 149 287 (accept_3_2 103 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 149
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 149 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 101 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 149 287 (accept_3_2 100 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 149 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 99 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 149 287 (accept_3_2 97 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 149 287
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 95 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 149 287 (accept_3_2 94 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 149 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 149 287 (accept_3_2 91 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 149 287
  (Polychromatic418967fa.accept_14_5_9_7_1_590 89 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 149 287 (accept_3_2 88 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 149 287 (accept_3_2 85 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 149 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 149 287 (accept_3_2 82 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 149 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 81 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 149 287 (Polychromatic418967fa.accept_13_2_6_1_1_3807 80 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 287 (accept_3_2 79 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 149 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 287
  (Polychromatic418967fa.accept_20_17_9_7_1_13576 77 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 149 287 (accept_3_2 76 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 149 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 149 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 287 (accept_3_2 73 149 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 287 (Polychromatic418967fa.accept_10_2_9_7_1_720
  72 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 287
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 149 287 (accept_3_2 70 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 149 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 68 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 287 (accept_3_2 67 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 149 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 287 (accept_3_2 64 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 287 (accept_3_2 61 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 287
  (Polychromatic418967fa.accept_13_7_6_1_1_368 59 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 287 (accept_3_2 58 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 287 (accept_3_2 55 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 287
  (Polychromatic418967fa.accept_17_2_13_15_1_4349 53 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 149 287 (accept_3_2 52 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 149 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 149 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 287 (accept_3_2 49 149 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48
  149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 287 (accept_3_2 46 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 287 (Polychromatic418967fa.accept_17_11_13_15_1_2140 45 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 44 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 287 (accept_3_2 43 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 149 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 287
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 287 (accept_3_2 40 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 287 (accept_3_2 37 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 287 (Polychromatic418967fa.accept_16_4_5_15_1_5083 36 149 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 287
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 287 (accept_3_2 34 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 287 (accept_3_2 31 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 287 (accept_3_2 28 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 287 (accept_3_2 25 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 287
  (Polychromatic418967fa.accept_19_4_16_2_1_6967 23 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 287 (accept_3_2 22 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 287 (accept_3_2 19 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 287
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 17 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 287 (accept_3_2 16 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 287 (accept_3_2 13 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 287 (accept_3_2 10 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 287 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 287 (accept_3_2 7 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 287
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 287 (accept_3_2 4 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 149 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 287 (accept_3_2 1 149 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 140 148 287 (Eq.refl Bool.true) (allA_of_3_0 140 148 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 141 147 287 (Eq.refl Bool.true) (allA_succ_of_gcd 140 147 287 7 20 21 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 139 147 287 (accept_3_2 139 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 147 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 138 147
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 147 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 137 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 136 147 287 (accept_3_2 136 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  135 147 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 135 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 134 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 134 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 133 147 287 7 19 21 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 132 147 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 132 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 147 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 131 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 147 287 (accept_3_2 130 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 147 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 129 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 147 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 128 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 147 287 (accept_3_2 127 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  126 147 287 7 18 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 125 147 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 125 147 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 147 287 (accept_3_2 124 147 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 123 147 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 123 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 147 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 122 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 147 287 (accept_3_2 121 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 147 287 (Polychromatic418967fa.accept_13_3_4_1_1_363 120 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 119 147 287 7 17 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 118 147 287 (accept_3_2 118 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 147 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 117 147 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26
  116 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 147 287 (accept_3_2
  115 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 147 287
  (Polychromatic418967fa.accept_9_6_3_8_1_595 114 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 147 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 113 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 147 287 7 16 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 147 287
  (Polychromatic418967fa.accept_15_6_12_2_1_2803 111 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 147 287 (accept_3_2 109 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 147 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 108 147
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 147 287
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 107 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 147 287 (accept_3_2 106 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  105 147 287 7 15 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 104 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 287 (accept_3_2 103 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 147 287 (Polychromatic418967fa.accept_19_7_14_2_1_4095 102 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 147 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 101 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 147 287 (accept_3_2 100 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 147 287 (Polychromatic418967fa.accept_19_4_14_2_1_4117 99 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 147 287 7 14 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 147 287 (accept_3_2 97 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 147 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 147 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 147 287 (accept_3_2 94 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 147 287
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 93 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 147 287 7 13 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 147 287
  (Polychromatic418967fa.accept_17_5_11_15_1_5445 90 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 147 287 (Polychromatic418967fa.accept_15_14_12_2_1_3804 89 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 287 (accept_3_2 88 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 147 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 147 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 147 287 (accept_3_2 85 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84
  147 287 7 12 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 147 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 287 (accept_3_2 82 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 147 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 147 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 147 287 (accept_3_2 79 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 147 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 77 147 287 7 11 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 147 287 (accept_3_2 76 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 147 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 75 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 287 (accept_3_2 73 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 287
  (Polychromatic418967fa.accept_17_4_11_15_1_3170 72 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 147 287 (Polychromatic418967fa.accept_16_7_3_15_1_2940 71 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 147 287 7 10 21 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 147 287
  (Polychromatic418967fa.accept_9_6_3_8_1_595 69 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 287 (accept_3_2 67 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 147 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 66 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 287 (accept_3_2 64 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63
  147 287 7 9 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  62 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 147 287 (accept_3_2 61 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 147 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 287 (accept_3_2 58 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 287
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 147 287 7 8 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 147 287 (accept_3_2 55 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 147 287 (Polychromatic418967fa.accept_19_16_14_2_1_6924 54 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 147 287 (Polychromatic418967fa.accept_22_9_15_1_1_13101 53 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 287 (accept_3_2 52 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 147 287 7 7 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 147 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 287 (accept_3_2 46 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 287
  (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 287 (accept_3_2 43 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 147 287 7 6 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 147 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 287 (accept_3_2 40 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 287 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 147
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 287 (accept_3_2 37 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 147 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 147 287 7 5 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 147 287 (accept_3_2 34 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 147 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 287 (accept_3_2 31 147 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000
  30 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 147 287 7 4 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 147 287 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 147 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 26
  147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 287 (accept_3_2 25
  147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 287
  (Polychromatic418967fa.accept_9_6_3_8_1_595 24 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 287 (accept_3_2 22 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 147 287 7 3 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 287 (accept_3_2 19 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 147
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 287
  (Polychromatic418967fa.accept_19_17_14_2_1_4116 17 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 147 287 (accept_3_2 16 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 147 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 147 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 147 287 7 2 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 147 287 (accept_3_2 13 147 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 147 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 287 (accept_3_2 10 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147 287 7 1 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 147 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6
  147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 287 (accept_3_2 4 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 287 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 147 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 147 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 287 (accept_3_2 1 147 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 142 146 287 (Eq.refl Bool.true) (allA_succ_of_accept 141 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  141 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 140 146 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 140 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 139 146 287 (accept_3_2 139 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  138 146 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 138 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 137 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 137 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 146 287 (accept_3_2 136 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 135 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 135 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 146 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 134 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 146 287 (accept_3_2 133 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  132 146 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 132 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 131 146 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 131 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 146 287 (accept_3_2 130 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 129 146 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 146 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 128 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 146 287 (accept_3_2 127 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  126 146 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 126 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 125 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 125 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 146 287 (accept_3_2 124 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 123 146
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 146 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 122 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 146 287 (accept_3_2 121 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 146 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 120 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 146 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 119 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 146 287 (accept_3_2 118 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 146 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 146 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 116 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 146 287 (accept_3_2 115 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 146 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 114 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 113 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 146 287 (accept_3_2 112 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 111 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 146 287
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 110 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 146 287 (accept_3_2 109 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 146 287 (Polychromatic418967fa.accept_13_4_3_1_1_2898 108 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 146 287 (Polychromatic418967fa.accept_17_5_10_15_1_5574 107 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 146 287 (accept_3_2 106 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 146 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 146 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 104 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 146 287 (accept_3_2 103 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 146 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 146 287 (accept_3_2 100 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 146 287
  (Polychromatic418967fa.accept_13_7_3_1_1_814 98 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 146 287 (accept_3_2 97 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 146 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 146 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 146 287 (accept_3_2 94 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 146 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 92 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 146 287 (accept_3_2 91 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 146 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 90 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 146 287 (accept_3_2 88 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 146 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 146 287 (accept_3_2 85 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 146 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 146 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 83 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 146 287 (accept_3_2 82 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 146 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 146 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 146 287 (accept_3_2 79 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 146 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 146 287 (accept_3_2 76 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 146 287
  (Polychromatic418967fa.accept_21_11_20_14_1_4179 74 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 146 287 (accept_3_2 73 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 146 287 (Polychromatic418967fa.accept_13_7_3_1_1_814 72 146 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 146 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 71 146
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 146 287 (accept_3_2 70 146
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  69 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 146 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 146 287 (accept_3_2 67 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 146 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 146 287 (accept_3_2 64 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 146 287
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 62 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 146 287 (accept_3_2 61 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 146 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 146 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 146 287 (accept_3_2 58 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 146 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 146 287 (accept_3_2 55 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 146 287 (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 146 287 (accept_3_2 52 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 146 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 146 287 (accept_3_2 49 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 146 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 146 287 (Polychromatic418967fa.accept_18_11_2_17_1_3490 47 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 146 287 (accept_3_2 46 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 146 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 146 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 146 287 (accept_3_2 43 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 287 (accept_3_2 40 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 287
  (Polychromatic418967fa.accept_17_4_10_15_1_5444 38 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 146 287 (accept_3_2 37 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 146 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 146 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 146 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 146
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 287 (accept_3_2 34 146
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  33 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 287 (accept_3_2 31 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 287 (accept_3_2 28 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 287
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 146 287 (accept_3_2 25 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 146 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 146 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 287 (accept_3_2 22 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 146 287 (accept_3_2 19 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 146 287 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 287 (accept_3_2 16 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 146 287 (accept_3_2 13 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 146 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 146 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 287 (accept_3_2 10 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 287
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 287 (accept_3_2 7 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 287 (accept_3_2 4 146 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 146 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 287
  (Polychromatic418967fa.accept_11_2_3_1_1_244 2 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 287 (accept_3_2 1 146 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 143 145 287 (Eq.refl Bool.true) (allA_of_3_0 143 145 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 144 287 (allA_succ_of_accept 143 144 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 143 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 142 144 287 (accept_3_2 142 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 141 144 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 141 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 140 144 287
  (Polychromatic418967fa.accept_22_8_12_1_1_13175 140 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 139 144 287 (accept_3_2 139 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 138 144 287 (Polychromatic418967fa.accept_21_12_18_14_1_8854 138 144 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 144 287
  (Polychromatic418967fa.accept_14_11_4_7_1_609 137 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 136 144 287 (accept_3_2 136 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  135 144 287 (Polychromatic418967fa.accept_21_9_18_14_1_5648 135 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 134 144 287 (Polychromatic418967fa.accept_22_2_12_1_1_17636 134 144 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 144 287 (accept_3_2 133 144 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 144 287 (Polychromatic418967fa.accept_10_2_4_7_1_352
  132 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 144 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 131 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 144 287 (accept_3_2 130 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 144 287 (Polychromatic418967fa.accept_14_3_4_7_1_175 129 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 144 287 (Polychromatic418967fa.accept_15_8_9_2_1_1897 128 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 144 287 (accept_3_2 127 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 144 287 (Polychromatic418967fa.accept_22_16_12_1_1_13174 126
  144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 144 287
  (Polychromatic418967fa.accept_17_6_8_15_1_10655 125 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 144 287 (accept_3_2 124 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 144 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 123 144 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 144 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 122 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 144 287 (accept_3_2 121 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 144 287
  (Polychromatic418967fa.accept_21_15_18_14_1_5632 120 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 144 287 (Polychromatic418967fa.accept_22_9_12_1_1_13192 119 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 144 287 (accept_3_2 118 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 144 287 (Polychromatic418967fa.accept_19_3_11_2_1_12523 117
  144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 144 287
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 116 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 144 287 (accept_3_2 115 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 144 287 (Polychromatic418967fa.accept_21_9_18_14_1_5648 114 144 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 144 287 (Polychromatic418967fa.accept_10_3_4_7_1_353
  113 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 144 287 (accept_3_2
  112 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 144 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 111 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 144 287 (Polychromatic418967fa.accept_19_15_11_2_1_12506 110 144 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 144 287 (accept_3_2 109 144 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 144 287 (Polychromatic418967fa.accept_14_10_4_7_1_1214 108 144 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 144 287
  (Polychromatic418967fa.accept_22_19_12_1_1_11606 107 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 144 287 (accept_3_2 106 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 144 287 (Polychromatic418967fa.accept_19_10_11_2_1_8354 105 144 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 144 287
  (Polychromatic418967fa.accept_19_9_11_2_1_5436 104 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 144 287 (accept_3_2 103 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 144 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 102 144 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 144 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 101 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 144 287 (accept_3_2 100 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 144 287
  (Polychromatic418967fa.accept_19_4_11_2_1_11111 99 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 144 287 (Polychromatic418967fa.accept_15_8_9_2_1_1897 98 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 144 287 (accept_3_2 97 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 144 287 (Polychromatic418967fa.accept_21_12_18_14_1_8854 96
  144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 144 287
  (Polychromatic418967fa.accept_14_11_4_7_1_609 95 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 144 287 (accept_3_2 94 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 144 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 93 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 144 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 92 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 144 287 (accept_3_2 91 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 144 287 (Polychromatic418967fa.accept_21_6_18_14_1_14768 90
  144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 144 287
  (Polychromatic418967fa.accept_19_13_11_2_1_4112 89 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 144 287 (accept_3_2 88 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 144 287 (Polychromatic418967fa.accept_14_3_4_7_1_175 87 144 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 144 287 (Polychromatic418967fa.accept_15_11_9_2_1_4780 86 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 144 287 (accept_3_2 85 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 144 287
  (Polychromatic418967fa.accept_19_8_11_2_1_6876 84 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 144 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 83 144 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 144 287 (accept_3_2 82 144 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 144 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 81 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 144 287
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 80 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 144 287 (accept_3_2 79 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 144 287 (Polychromatic418967fa.accept_17_10_8_15_1_8104 78 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 144 287 (Polychromatic418967fa.accept_20_17_4_7_1_4808 77 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 144 287 (accept_3_2 76 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 144 287 (Polychromatic418967fa.accept_21_12_18_14_1_8854 75
  144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 144 287
  (Polychromatic418967fa.accept_17_6_8_15_1_10655 74 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 144 287 (accept_3_2 73 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 144 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 144 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 144 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 71 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 144 287 (accept_3_2 70 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 144 287
  (Polychromatic418967fa.accept_21_6_18_14_1_14768 69 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 144 287 (Polychromatic418967fa.accept_15_8_9_2_1_1897 68 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 144 287 (accept_3_2 67 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 144 287 (Polychromatic418967fa.accept_14_10_4_7_1_1214 66 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 144 287
  (Polychromatic418967fa.accept_19_8_11_2_1_6876 65 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 144 287 (accept_3_2 64 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 144 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 144 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 287 (accept_3_2 61 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 144 287 (Polychromatic418967fa.accept_19_3_11_2_1_12523 60 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 144 287
  (Polychromatic418967fa.accept_14_3_4_7_1_175 59 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 144 287 (accept_3_2 58 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 144 287 (Polychromatic418967fa.accept_17_6_8_15_1_10655 57 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 144 287 (Polychromatic418967fa.accept_15_11_9_2_1_4780 56 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 144 287 (accept_3_2 55 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 144 287 (Polychromatic418967fa.accept_19_16_11_2_1_12465 54
  144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 144 287
  (Polychromatic418967fa.accept_10_3_4_7_1_353 53 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 144 287 (accept_3_2 52 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 144 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 144 287 (Polychromatic418967fa.accept_26_24_14_1_1_8552 50 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 287 (accept_3_2 49 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 144 287 (Polychromatic418967fa.accept_19_10_11_2_1_8354 48 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 144 287
  (Polychromatic418967fa.accept_17_13_8_15_1_8135 47 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 144 287 (accept_3_2 46 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 144 287 (Polychromatic418967fa.accept_14_3_4_7_1_175 45 144 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 287 (Polychromatic418967fa.accept_17_10_8_15_1_8104 44 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 287 (accept_3_2 43 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 144 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 144 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 41 144 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 287 (accept_3_2 40 144 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 144 287 (Polychromatic418967fa.accept_14_11_4_7_1_609 39 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 287
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 38 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 144 287 (accept_3_2 37 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 144 287 (Polychromatic418967fa.accept_21_15_18_14_1_5632 36 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 144 287 (Polychromatic418967fa.accept_19_16_11_2_1_12465 35 144 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 287 (accept_3_2 34 144 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 287 (Polychromatic418967fa.accept_10_3_4_7_1_353
  33 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 287
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 144 287 (accept_3_2 31 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 144 287 (Polychromatic418967fa.accept_17_13_8_15_1_8135 30 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 144 287 (Polychromatic418967fa.accept_19_10_11_2_1_8354 29 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 287 (accept_3_2 28 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 287 (Polychromatic418967fa.accept_17_10_8_15_1_8104 27 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 287
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 144 287 (accept_3_2 25 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 144 287 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 144 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 287 (accept_3_2 22 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 287
  (Polychromatic418967fa.accept_21_20_18_14_1_10455 20 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 144 287 (accept_3_2 19 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 144 287 (Polychromatic418967fa.accept_23_18_6_11_1_14518 18 144 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 287 (Polychromatic418967fa.accept_14_3_4_7_1_175
  17 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 287 (accept_3_2 16
  144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 287
  (Polychromatic418967fa.accept_19_15_11_2_1_12506 15 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 144 287 (Polychromatic418967fa.accept_25_14_19_12_1_10783 14 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 287 (accept_3_2 13 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 144
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 287 (accept_3_2 10 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  144 287 (Polychromatic418967fa.accept_19_9_11_2_1_5436 9 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 144 287 (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 144 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 287 (accept_3_2 7 144 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 287 (Polychromatic418967fa.accept_17_6_8_15_1_10655 6 144 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 287
  (Polychromatic418967fa.accept_21_5_18_14_1_2793 5 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 287 (accept_3_2 4 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  144 287 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 144 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 144 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 144 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 287 (accept_3_2 1 144 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 144
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 143 287 (allA_succ_of_accept 142 143 287 (accept_3_2 142 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 141 143 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 141 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 140 143 287 (Polychromatic418967fa.accept_22_8_11_1_1_17635 140
  143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 139 143 287 (accept_3_2 139
  143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 138 143 287
  (Polychromatic418967fa.accept_17_2_7_15_1_5525 138 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 137 143 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 137 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 143 287 (accept_3_2 136 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 143 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 135 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 143 287
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 134 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 133 143 287 (accept_3_2 133 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  132 143 287 (Polychromatic418967fa.accept_19_18_10_2_1_2850 132 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 131 143 287 (Polychromatic418967fa.accept_19_17_10_2_1_9793 131 143 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 143 287 (accept_3_2 130 143 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 143 287
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 129 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 143 287 (Polychromatic418967fa.accept_17_9_7_15_1_4346 128 143 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 143 287 (accept_3_2 127 143 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 126 143 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 126 143 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 143 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 125 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 143 287 (accept_3_2 124 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 143 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 123 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 143 287 (Polychromatic418967fa.accept_14_10_3_7_1_1975 122 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 143 287 (accept_3_2 121 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 143 287 (Polychromatic418967fa.accept_19_6_10_2_1_6874 120
  143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 143 287
  (Polychromatic418967fa.accept_19_5_10_2_1_1731 119 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 143 287 (accept_3_2 118 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 143 287 (Polychromatic418967fa.accept_22_7_11_1_1_6711 117 143 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 143 287
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 116 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 143 287 (accept_3_2 115 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 143 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 114 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 143 287 (Polychromatic418967fa.accept_19_18_10_2_1_2850 113 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 143 287 (accept_3_2 112 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 143 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 111 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 143 287
  (Polychromatic418967fa.accept_20_10_3_7_1_10761 110 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 143 287 (accept_3_2 109 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 143 287 (Polychromatic418967fa.accept_14_10_3_7_1_1975 108 143 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 143 287
  (Polychromatic418967fa.accept_17_5_7_15_1_1230 107 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 143 287 (accept_3_2 106 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 143 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 105 143 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 143 287
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 104 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 143 287 (accept_3_2 103 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 143 287 (Polychromatic418967fa.accept_14_4_3_7_1_3702 102 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 143 287 (Polychromatic418967fa.accept_19_6_10_2_1_6874 101 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 143 287 (accept_3_2 100 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 143 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 99 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 143 287
  (Polychromatic418967fa.accept_22_10_11_1_1_14668 98 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 143 287 (accept_3_2 97 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 143 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 96 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 143 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 95 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 143 287 (accept_3_2 94 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 143 287
  (Polychromatic418967fa.accept_19_17_10_2_1_9793 93 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 143 287 (Polychromatic418967fa.accept_21_8_17_14_1_4156 92 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 143 287 (accept_3_2 91 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 143 287 (Polychromatic418967fa.accept_17_5_7_15_1_1230 90 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 287
  (Polychromatic418967fa.accept_19_13_10_2_1_12473 89 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 143 287 (accept_3_2 88 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 143 287 (Polychromatic418967fa.accept_17_2_7_15_1_5525 87 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 143 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 86 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 287 (accept_3_2 85 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 287
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 84 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 143 287 (Polychromatic418967fa.accept_21_20_17_14_1_10489 83 143 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 143 287 (accept_3_2 82 143 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 143 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 81 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 143 287
  (Polychromatic418967fa.accept_14_10_3_7_1_1975 80 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 143 287 (accept_3_2 79 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 143 287 (Polychromatic418967fa.accept_21_15_17_14_1_4191 78 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 77 143 287 (Polychromatic418967fa.accept_17_9_7_15_1_4346 77 143 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 287 (accept_3_2 76 143 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 143 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108
  75 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 287
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 74 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 143 287 (accept_3_2 73 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 143 287 (Polychromatic418967fa.accept_21_9_17_14_1_603 72 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 143 287 (Polychromatic418967fa.accept_21_8_17_14_1_4156 71 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 287 (accept_3_2 70 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 69 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 287
  (Polychromatic418967fa.accept_19_11_10_2_1_9757 68 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 143 287 (accept_3_2 67 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 143 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 66 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 287 (accept_3_2 64 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 287
  (Polychromatic418967fa.accept_19_6_10_2_1_6874 63 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 143 287 (Polychromatic418967fa.accept_19_5_10_2_1_1731 62 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 287 (accept_3_2 61 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 143 287 (Polychromatic418967fa.accept_14_4_3_7_1_3702 60 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 287
  (Polychromatic418967fa.accept_22_15_11_1_1_6777 59 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 143 287 (accept_3_2 58 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 143 287 (Polychromatic418967fa.accept_21_15_17_14_1_4191 57 143 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197
  56 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 287 (accept_3_2 55
  143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 287
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 143 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 53 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 287 (accept_3_2 52 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 143 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 51 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 287
  (Polychromatic418967fa.accept_19_12_10_2_1_12527 50 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 143 287 (accept_3_2 49 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 143 287 (Polychromatic418967fa.accept_22_4_11_1_1_11615 48 143 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 287
  (Polychromatic418967fa.accept_21_5_17_14_1_4178 47 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 143 287 (accept_3_2 46 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 143 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 287 (accept_3_2 43 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 287
  (Polychromatic418967fa.accept_26_16_13_1_1_17634 42 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 287 (Polychromatic418967fa.accept_21_20_17_14_1_10489 41 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 287 (accept_3_2 40 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 39 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 287
  (Polychromatic418967fa.accept_14_10_3_7_1_1975 38 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 287 (accept_3_2 37 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 287 (accept_3_2 34 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 287 (Polychromatic418967fa.accept_23_10_5_11_1_14502 33
  143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 287
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 32 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 287 (accept_3_2 31 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 287 (Polychromatic418967fa.accept_19_11_10_2_1_9757 30 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 287 (Polychromatic418967fa.accept_21_8_17_14_1_4156 29 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 287 (accept_3_2 28 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 287 (Polychromatic418967fa.accept_19_8_10_2_1_5414 27 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 287
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 287 (accept_3_2 25 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 287 (Polychromatic418967fa.accept_21_2_17_14_1_5644 23 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 287 (accept_3_2 22 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 287 (Polychromatic418967fa.accept_15_6_8_2_1_104 21 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 287
  (Polychromatic418967fa.accept_21_20_17_14_1_10489 20 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 143 287 (accept_3_2 19 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 143 287 (Polychromatic418967fa.accept_14_4_3_7_1_3702 18 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 287 (Polychromatic418967fa.accept_19_17_10_2_1_9793 17 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 287 (accept_3_2 16 143
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 143 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 287 (accept_3_2 13 143 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 143 287 (Polychromatic418967fa.accept_19_12_10_2_1_12527 12 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 287
  (Polychromatic418967fa.accept_14_11_3_7_1_604 11 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 287 (accept_3_2 10 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 287 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 287 (Polychromatic418967fa.accept_19_8_10_2_1_5414 8 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 287 (accept_3_2 7 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 143 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 287 (accept_3_2 4 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 287 (Polychromatic418967fa.accept_21_3_17_14_1_8828 3 143 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 287 (Polychromatic418967fa.accept_17_2_7_15_1_5525 2 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 287 (accept_3_2 1 143 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 143
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 142 287 (allA_of_3_0 142 142 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 141 287
  (allA_succ_of_accept 140 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 140 141 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 139 141 287 (accept_3_2 139 141 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 138 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 138 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 141 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 137 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 136 141 287 (accept_3_2 136 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  135 141 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 135 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 134 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 134 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 141 287 (accept_3_2 133 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 141 287 (Polychromatic418967fa.accept_14_6_1_7_1_2775 132 141
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 141 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 131 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 141 287 (accept_3_2 130 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 129 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 128 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 141 287 (accept_3_2 127 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 126 141
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 141 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 125 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 124 141 287 (accept_3_2 124 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 141 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 123 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27
  122 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 141 287 (accept_3_2
  121 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 141 287
  (Polychromatic418967fa.accept_9_3_6_8_1_308 120 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 141 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 119 141 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 141 287 (accept_3_2 118 141 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 141 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 117 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 141 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 116 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 141 287 (accept_3_2 115 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 141 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 113 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 141 287 (accept_3_2 112 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 111 141
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 141 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 141 287 (accept_3_2 109 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 141 287 (Polychromatic418967fa.accept_16_12_13_15_1_1966 108 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 141 287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 107 141 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 141 287 (accept_3_2 106 141 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 141 287
  (Polychromatic418967fa.accept_19_10_8_2_1_831 105 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 141 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 287 (accept_3_2 103 141 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 141 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 141 287 (accept_3_2 100 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 141 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 287 (accept_3_2 97 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 96 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 141 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 141 287 (accept_3_2 94 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 287 (accept_3_2 91 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 141 287
  (Polychromatic418967fa.accept_19_13_8_2_1_4089 89 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 141 287 (accept_3_2 88 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 141 287 (Polychromatic418967fa.accept_11_10_9_1_1_2186 87 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 287 (accept_3_2 85 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 141 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 141 287 (accept_3_2 82 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 141 287 (Polychromatic418967fa.accept_13_3_11_1_1_2122 81 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 287 (accept_3_2 79 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 287 (accept_3_2 76 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 287 (accept_3_2 73 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 141 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 287
  (Polychromatic418967fa.accept_15_11_6_2_1_1106 71 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 141 287 (accept_3_2 70 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 141 287 (Polychromatic418967fa.accept_14_13_1_7_1_1211 69 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 287 (accept_3_2 67 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 287 (accept_3_2 64 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 141 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 287 (accept_3_2 61 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 141 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 287 (accept_3_2 58 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 287 (accept_3_2 55 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 287
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 287 (accept_3_2 52 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 141 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 287 (accept_3_2 49 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 287 (accept_3_2 46 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 287 (Polychromatic418967fa.accept_17_11_5_15_1_8144 45 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 287 (accept_3_2 43 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 287 (accept_3_2 40 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 287 (accept_3_2 37 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 287
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 287 (accept_3_2 34 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 33 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 287 (accept_3_2 31 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 287 (accept_3_2 28 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 287 (accept_3_2 25 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 287 (accept_3_2 22 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 287 (accept_3_2 19 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 287
  (Polychromatic418967fa.accept_21_17_15_14_1_5707 17 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 141 287 (accept_3_2 16 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 141 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 141 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 287 (accept_3_2 13 141 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308
  12 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 287 (accept_3_2 10 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 287 (accept_3_2 7 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 287 (accept_3_2 4 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 141 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 287 (accept_3_2 1 141 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 140 287 (allA_succ_of_accept 139 140 287 (accept_3_2 139 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 138 140 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 138 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 137 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 137 140
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 140 287 (accept_3_2 136 140
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 135 140 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 135 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 140 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 134 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 133 140 287 7 19 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 132 140 287 (Polychromatic418967fa.accept_9_6_5_8_1_598
  132 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 140 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 131 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 140 287 (accept_3_2 130 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 129 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 128 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 140 287 (accept_3_2 127 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 140 287 7 18 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 140 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  125 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 140 287 (accept_3_2
  124 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 140 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 123 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 140 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 122 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 140 287 (accept_3_2 121 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 140 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 120 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 119 140 287 7 17 20 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 118 140 287 (accept_3_2 118 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32
  117 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 140 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 116 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 140 287 (accept_3_2 115 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 140 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 114 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 140 287 (Polychromatic418967fa.accept_13_9_10_1_1_1389 113 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 140 287 7 16 20 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 140 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 140 287 (accept_3_2 109 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 140 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 108 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 140 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 107 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 140 287 (accept_3_2 106 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  105 140 287 7 15 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 104 140 287 (Polychromatic418967fa.accept_15_14_5_2_1_4761 104 140 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 140 287 (accept_3_2 103 140 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 140 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 140 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 101 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 140 287 (accept_3_2 100 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 140 287 7 14 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 140 287 (accept_3_2 97 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 140 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 140 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 95 140
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 140 287 (accept_3_2 94 140
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 140 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 93 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 91 140 287 7 13 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 140 287
  (Polychromatic418967fa.accept_19_14_7_2_1_11116 90 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 140 287 (Polychromatic418967fa.accept_13_11_10_1_1_1409 89 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 140 287 (accept_3_2 88 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 140 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 86 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 140 287 (accept_3_2 85 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84
  140 287 7 12 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 140 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 140 287 (accept_3_2 82 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 140 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 140 287 (Polychromatic418967fa.accept_19_4_7_2_1_6944
  80 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 140 287 (accept_3_2 79
  140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 140 287
  (Polychromatic418967fa.accept_9_6_5_8_1_598 78 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 140 287 7 11 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 140 287 (accept_3_2 76 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 140 287 (accept_3_2 73 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 140 287
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 72 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 140 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 71 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 287 7 10 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69
  140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 140 287
  (Polychromatic418967fa.accept_16_4_12_15_1_6289 68 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 140 287 (accept_3_2 67 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 140 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 140 287 (accept_3_2 64 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 140 287 7 9 20 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 140 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 140 287 (accept_3_2 61 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 140 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 140 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 140 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 140 287 (accept_3_2 58 140 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 140 287 7 8 20 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 140 287 (accept_3_2 55 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 140 287
  (Polychromatic418967fa.accept_19_16_7_2_1_12512 54 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 140 287 (Polychromatic418967fa.accept_17_2_4_15_1_5451 53 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 140 287 (accept_3_2 52 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 140 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 140 287 7 7 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 140 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 287 (accept_3_2 46 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 140 287
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 44 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 140 287 (accept_3_2 43 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  140 287 7 6 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 140 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 140 287 (accept_3_2 40 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 287 (accept_3_2 37 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 140 287
  (Polychromatic418967fa.accept_16_4_12_15_1_6289 36 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 140 287 7 5 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 140 287 (accept_3_2 34 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 287 (Polychromatic418967fa.accept_19_13_7_2_1_5413 32 140
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 140 287 (accept_3_2 31 140
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 140 287
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 287 7 4 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 287
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 140 287 (accept_3_2 25 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 140 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 287 (Polychromatic418967fa.accept_19_4_7_2_1_6944 23 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 287 (accept_3_2 22 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 140 287 7 3 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 140 287 (accept_3_2 19
  140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 287
  (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 140 287 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 287 (accept_3_2 16 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 287 7 2 20 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 287 (accept_3_2 13 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 140 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 140 287 (accept_3_2 10 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 140 287 (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 140 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 140 287 7 1 20 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 140 287
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 140 287 (Polychromatic418967fa.accept_19_5_7_2_1_1728 5 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 287 (accept_3_2 4 140 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 140 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2
  140 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 287 (accept_3_2 1 140
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 139 287 (allA_of_3_0 139 139 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 138 287
  (allA_succ_of_accept 137 138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 137 138 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 136 138 287 (accept_3_2 136 138 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 135 138 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 135 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 138 287
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 134 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 133 138 287 (accept_3_2 133 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 132 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 132 138 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 138 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 131 138
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 138 287 (accept_3_2 130 138
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 129 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 138 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 128 138 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 138 287 (accept_3_2 127 138 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 138 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 126 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 125 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 138 287 (accept_3_2 124 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 123 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 138 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 122 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 138 287 (accept_3_2 121 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 138 287 (Polychromatic418967fa.accept_21_15_12_14_1_7232 120
  138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 138 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 119 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 138 287 (accept_3_2 118 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 138 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 116 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 138 287 (accept_3_2 115 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 114 138
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 138 287 (accept_3_2 112 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 138 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 111 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 138 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 110 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 138 287 (accept_3_2 109 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 138 287 (Polychromatic418967fa.accept_21_3_12_14_1_8848 108
  138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 138 287
  (Polychromatic418967fa.accept_14_9_12_7_1_597 107 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 138 287 (accept_3_2 106 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 138 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 104 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 138 287 (accept_3_2 103 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 138 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 102
  138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 138 287 (accept_3_2 100 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 138 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 99 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 138 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 98 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 138 287 (accept_3_2 97 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 138 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 138 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 95 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 138 287 (accept_3_2 94 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 138 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 92 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 138 287 (accept_3_2 91 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 138 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 90 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 138 287 (accept_3_2 88 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 138 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 86 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 138 287 (accept_3_2 85 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 138 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 84 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 138 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 138 287 (accept_3_2 82 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 138 287 (Polychromatic418967fa.accept_15_5_3_2_1_5930 80 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 138 287 (accept_3_2 79 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 138 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 138 287 (accept_3_2 76 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 138 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 75 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 138 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 74 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 138 287 (accept_3_2 73 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 138 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 72 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 138 287
  (Polychromatic418967fa.accept_11_5_6_1_1_988 71 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 138 287 (accept_3_2 70 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 138 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 68 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 138 287 (accept_3_2 67 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 138 287 (Polychromatic418967fa.accept_21_3_12_14_1_8848 66 138 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 138 287 (accept_3_2 64 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 138 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 63 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 138 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 62 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 138 287 (accept_3_2 61 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 138 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 138 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 138 287 (accept_3_2 58 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 138 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 287 (accept_3_2 55 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 138 287 (Polychromatic418967fa.accept_19_16_5_2_1_8375 54 138 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 138 287 (accept_3_2 52 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 138 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 287 (accept_3_2 49 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 48 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 138 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 138 287 (accept_3_2 46 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 138 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 287 (accept_3_2 43 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 138 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 138 287 (accept_3_2 40 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 138 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 39 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 138 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 287 (accept_3_2 37 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 138 287 (Polychromatic418967fa.accept_19_17_5_2_1_2843 36 138 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 138 287
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 138 287 (accept_3_2 34 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 138 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 287 (accept_3_2 31 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 287 (Polychromatic418967fa.accept_14_2_12_7_1_617 30 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 138 287 (accept_3_2 28 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 138 287 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 138 287 (Polychromatic418967fa.accept_19_7_5_2_1_2842 26 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 287 (accept_3_2 25 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 138 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 138 287 (accept_3_2 22 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 138 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 287 (accept_3_2 19 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 287 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 138 287 (accept_3_2 16 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 138 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 287 (accept_3_2 13 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 287 (accept_3_2 10 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  138 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 138 287 (Polychromatic418967fa.accept_19_8_5_2_1_4105 8 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 287 (accept_3_2 7 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 138 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 287 (accept_3_2 4 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  138 287 (Polychromatic418967fa.accept_19_3_5_2_1_4103 3 138 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 138 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 287 (accept_3_2 1 138 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 138
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 137 287 (allA_succ_of_accept 136 137 287 (accept_3_2 136 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 135 137 287 (Polychromatic418967fa.accept_17_16_1_15_1_5541 135 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 134 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27
  134 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 137 287 (accept_3_2
  133 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 132 137 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 132 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 131 137 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 131 137 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 137 287 (accept_3_2 130 137 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 129 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 137 287
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 128 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 127 137 287 (accept_3_2 127 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 126 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 126 137 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 137 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 125 137
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 137 287 (accept_3_2 124 137
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 137 287
  (Polychromatic418967fa.accept_9_6_2_8_1_592 123 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 122 137 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 137 287 (accept_3_2 121 137 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 120 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 137 287
  (Polychromatic418967fa.accept_19_5_4_2_1_6840 119 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 137 287 (accept_3_2 118 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 137 287 (Polychromatic418967fa.accept_21_12_11_14_1_7239 117 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 116 137 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 116 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 137 287 (accept_3_2 115 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27
  114 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 137 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 113 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 137 287 (accept_3_2 112 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 111 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 137 287 (accept_3_2 109 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 137 287 (Polychromatic418967fa.accept_14_10_11_7_1_1955 108
  137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 137 287
  (Polychromatic418967fa.accept_13_3_7_1_1_334 107 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 137 287 (accept_3_2 106 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 137 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 105 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 137 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 137 287 (accept_3_2 103 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 137
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 137 287
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 101 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 137 287 (accept_3_2 100 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 137 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 99 137 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 137 287 (accept_3_2 97 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 137 287 (Polychromatic418967fa.accept_9_6_2_8_1_592
  96 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 137 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 137 287 (accept_3_2 94 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 137 287 (Polychromatic418967fa.accept_18_2_11_17_1_4773 92 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 137 287 (accept_3_2 91 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 137 287
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 89 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 137 287 (accept_3_2 88 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 137 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 137 287 (accept_3_2 85 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 83 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 137 287 (accept_3_2 82 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 137 287 (Polychromatic418967fa.accept_13_3_7_1_1_334 81 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 137 287 (Polychromatic418967fa.accept_14_10_11_7_1_1955 80 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 287 (accept_3_2 79 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 137 287 (accept_3_2 76 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 287 (accept_3_2 73 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 287
  (Polychromatic418967fa.accept_13_6_7_1_1_335 71 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 137 287 (accept_3_2 70 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 137 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 137 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 287 (accept_3_2 67 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 287
  (Polychromatic418967fa.accept_21_2_11_14_1_11805 65 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 137 287 (accept_3_2 64 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 137 287 (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 137 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 287 (accept_3_2 61 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 287 (Polychromatic418967fa.accept_9_6_2_8_1_592
  60 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 137 287 (accept_3_2 58 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 287 (Polychromatic418967fa.accept_16_8_9_15_1_5112 56 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 287 (accept_3_2 55 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 287
  (Polychromatic418967fa.accept_22_9_5_1_1_2204 53 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 287 (accept_3_2 52 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 287 (accept_3_2 49 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 287
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 47 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 287 (accept_3_2 46 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 287 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 287 (Polychromatic418967fa.accept_19_6_4_2_1_1726 44 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 287 (accept_3_2 43 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 287 (accept_3_2 40 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 287 (accept_3_2 37 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 287 (Polychromatic418967fa.accept_19_17_4_2_1_8360 36 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 287
  (Polychromatic418967fa.accept_19_16_4_2_1_4102 35 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 287 (accept_3_2 34 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 287 (accept_3_2 31 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 287
  (Polychromatic418967fa.accept_13_3_7_1_1_334 29 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 287 (accept_3_2 28 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 287 (Polychromatic418967fa.accept_21_6_11_14_1_11812 27 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 287 (accept_3_2 25 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 287 (accept_3_2 22 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 287 (Polychromatic418967fa.accept_17_3_1_15_1_6835 20 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 287 (accept_3_2 19 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 287 (accept_3_2 16 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 287 (accept_3_2 13 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 287
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 287 (accept_3_2 10 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 287 (Polychromatic418967fa.accept_17_9_1_15_1_3156 9 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 287 (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 287 (accept_3_2 7 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 287 (accept_3_2 4 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 137 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 287 (accept_3_2 1 137 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 136 287 (allA_of_3_0 136 136 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 135 287
  (allA_succ_of_accept 134 135 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 134 135 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 135 287 (accept_3_2 133 135 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 135 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 132 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 135 287
  (Polychromatic418967fa.accept_14_5_9_7_1_590 131 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 135 287 (accept_3_2 130 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 135 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 129 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 128 135 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 128 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 135 287 (accept_3_2 127 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 135 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 126 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 135 287
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 125 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 135 287 (accept_3_2 124 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 135 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 123 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 135 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 122 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 135 287 (accept_3_2 121 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 135 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 120 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 135 287
  (Polychromatic418967fa.accept_22_9_3_1_1_13184 119 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 135 287 (accept_3_2 118 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 135 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 117 135 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 135 287 (Polychromatic418967fa.accept_6_2_3_5_1_26
  116 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 135 287 (accept_3_2
  115 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 135 287
  (Polychromatic418967fa.accept_14_2_9_7_1_5633 114 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 135 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 113 135 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 135 287 (accept_3_2 112 135 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 135 287 (Polychromatic418967fa.accept_21_6_9_14_1_8867 111 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 110 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 135 287 (accept_3_2 109 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 135 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 108 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 135 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 107 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 135 287 (accept_3_2 106 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 135 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 105
  135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 104 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 135 287 (accept_3_2 103 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 135 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 102 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 135 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 101 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 135 287 (accept_3_2 100 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 135 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 99 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 98 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 135 287 (accept_3_2 97 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 135 287 (Polychromatic418967fa.accept_14_12_9_7_1_2762 96 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 135 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 95 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 135 287 (accept_3_2 94 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 135 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 93 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 135 287 (accept_3_2 91 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 135 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 90 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 135 287 (Polychromatic418967fa.accept_14_5_9_7_1_590 89 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 287 (accept_3_2 88 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 287 (Polychromatic418967fa.accept_13_9_5_1_1_1382 87 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 135 287 (accept_3_2 85 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 135 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 84 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 135 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 83 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 287 (accept_3_2 82 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 135 287 (accept_3_2 79 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 135 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 78 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 135 287 (Polychromatic418967fa.accept_13_12_5_1_1_1383 77 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 287 (accept_3_2 76 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 135 287 (Polychromatic418967fa.accept_14_5_9_7_1_590 75 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 135 287 (accept_3_2 73 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 135 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 135 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 71 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 287 (accept_3_2 70 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 135 287 (accept_3_2 67 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 135 287 (Polychromatic418967fa.accept_18_12_9_17_1_7428 66 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 135 287 (Polychromatic418967fa.accept_17_14_16_15_1_5509 65 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 287 (accept_3_2 64 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 287 (accept_3_2 61 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 135 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 60 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 135 287 (Polychromatic418967fa.accept_16_11_7_15_1_1998 59 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 287 (accept_3_2 58 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 135 287 (accept_3_2 55 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 135 287 (Polychromatic418967fa.accept_14_12_9_7_1_2762 54 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 135 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 53 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 287 (accept_3_2 52 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 287 (Polychromatic418967fa.accept_13_12_5_1_1_1383 51 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 287 (accept_3_2 49 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 135 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 287 (Polychromatic418967fa.accept_13_8_5_1_1_1381 47 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 287 (accept_3_2 46 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 287 (accept_3_2 43 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 135 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 135 287 (Polychromatic418967fa.accept_20_1_15_7_1_3405 41 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 287 (accept_3_2 40 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 287 (Polychromatic418967fa.accept_21_18_9_14_1_8832 39 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 287 (accept_3_2 37 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 287 (Polychromatic418967fa.accept_21_15_9_14_1_10462 36 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 287 (accept_3_2 34 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 287 (accept_3_2 31 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 30 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 287 (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 287 (accept_3_2 28 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 287 (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 287 (accept_3_2 25 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 287 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 287 (accept_3_2 22 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 287 (accept_3_2 19 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 287 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 287 (accept_3_2 16 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 287 (Polychromatic418967fa.accept_18_15_9_17_1_6043 15 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 287 (accept_3_2 13 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 287 (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 287 (accept_3_2 10 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 135
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 287 (accept_3_2 7 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 287 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 287 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 135 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 287 (accept_3_2 4 135 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 135 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 287 (accept_3_2 1 135 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 134 287 (allA_succ_of_accept 133 134 287 (accept_3_2 133 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 132 134 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 132 134 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 134 287 (Polychromatic418967fa.accept_10_1_4_7_1_374 131 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 134 287 (accept_3_2 130 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 129 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 129 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 134 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 128 134 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 134 287 (accept_3_2 127 134 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 126 134 287 (Polychromatic418967fa.accept_19_12_1_2_1_9750 126 134 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 125 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 134 287 (accept_3_2 124 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 123 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 134 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 122 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 134 287 (accept_3_2 121 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 134 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 120
  134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 134 287
  (Polychromatic418967fa.accept_16_7_6_15_1_495 119 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 134 287 (accept_3_2 118 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 134 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 134 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 116 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 134 287 (accept_3_2 115 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 134 287 (Polychromatic418967fa.accept_13_10_4_1_1_2142 114
  134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 113 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 134 287 (accept_3_2 112 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 111 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 134 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 110 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 134 287 (accept_3_2 109 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 134 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 108
  134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 134 287
  (Polychromatic418967fa.accept_13_3_4_1_1_363 107 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 134 287 (accept_3_2 106 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 134 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 134 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 104 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 134 287 (accept_3_2 103 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 134 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 102 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 134 287 (accept_3_2 100 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 134 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 98 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 134 287 (accept_3_2 97 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 134 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 96 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 134 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 95 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 134 287 (accept_3_2 94 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 134 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 134 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 92 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 134 287 (accept_3_2 91 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 134 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 90 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 134 287 (accept_3_2 88 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 134 287 (Polychromatic418967fa.accept_21_2_8_14_1_4148 86 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 134 287 (accept_3_2 85 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 134 287 (Polychromatic418967fa.accept_19_8_1_2_1_13747 84 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 134 287
  (Polychromatic418967fa.accept_10_3_4_7_1_353 83 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 134 287 (accept_3_2 82 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 134 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 134 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 80 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 134 287 (accept_3_2 79 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 134 287 (Polychromatic418967fa.accept_15_3_14_2_1_1888 78 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 134 287 (accept_3_2 76 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 134 287 (Polychromatic418967fa.accept_18_2_8_17_1_4754 74 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 134 287 (accept_3_2 73 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 134 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 72 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 134 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 71 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 134 287 (accept_3_2 70 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 134 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 134 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 68 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 134 287 (accept_3_2 67 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 134 287 (Polychromatic418967fa.accept_19_9_1_2_1_6839 66 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 134 287 (accept_3_2 64 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 134 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 62 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 134 287 (accept_3_2 61 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 134 287 (Polychromatic418967fa.accept_19_3_1_2_1_6860 60 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 134 287
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 59 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 134 287 (accept_3_2 58 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 134 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 134 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 134 287 (accept_3_2 55 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 134 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 134 287 (accept_3_2 52 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 134 287 (Polychromatic418967fa.accept_15_5_14_2_1_1876 50 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 134 287 (accept_3_2 49 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 134 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 48 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 134 287
  (Polychromatic418967fa.accept_11_3_2_1_1_994 47 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 134 287 (accept_3_2 46 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 134 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 134 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 134 287 (accept_3_2 43 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 134 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 134 287 (accept_3_2 40 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 134 287 (Polychromatic418967fa.accept_18_2_8_17_1_4754 38 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 134 287 (accept_3_2 37 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 134 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 134 287
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 35 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 134 287 (accept_3_2 34 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 134 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 134 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 134 287 (accept_3_2 31 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 134 287 (Polychromatic418967fa.accept_23_7_19_11_1_17633 30
  134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 134 287 (accept_3_2 28 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 134 287 (Polychromatic418967fa.accept_19_7_1_2_1_9792 26 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 134 287 (accept_3_2 25 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 134 287 (Polychromatic418967fa.accept_21_3_8_14_1_8864 24 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 287
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 134 287 (accept_3_2 22 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 134 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 134 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 287 (accept_3_2 19 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 287 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 134 287 (accept_3_2 16 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 134 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 287 (accept_3_2 13 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 134
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 287
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 134 287 (accept_3_2 10 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  134 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 134 287 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 134 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 287 (accept_3_2 7 134 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 287 (Polychromatic418967fa.accept_14_6_8_7_1_589 6 134 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 134 287 (accept_3_2 4 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  134 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 134 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 134 287 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 134 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 287 (accept_3_2 1 134 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 134
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 133 287 (allA_of_3_0 133 133 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 132 287
  (allA_succ_of_accept 131 132 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 131 132 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 130 132 287 (accept_3_2 130 132 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 129 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 129 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 132 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 128 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 127 132 287 (accept_3_2 127 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  126 132 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 126 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 125 132 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 125 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 132 287 (accept_3_2 124 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 123 132 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 123 132
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 132 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 122 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 132 287 (accept_3_2 121 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 120 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 132 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 119 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 132 287 (accept_3_2 118 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 132 287 (Polychromatic418967fa.accept_16_5_4_15_1_1102 117
  132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 132 287
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 116 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 115 132 287 (accept_3_2 115 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 132 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 114 132 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 132 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 113 132
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 132 287 (accept_3_2 112 132
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 132 287
  (Polychromatic418967fa.accept_9_3_6_8_1_308 111 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 132 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 110 132 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 132 287 (accept_3_2 109 132 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 132 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 108 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 132 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 107 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 132 287 (accept_3_2 106 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 132 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 105 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 132 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 104 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 132 287 (accept_3_2 103 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 132
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 132 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 132 287 (accept_3_2 100 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 132 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 99 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 132 287 (Polychromatic418967fa.accept_19_3_18_2_1_6935 98 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 132 287 (accept_3_2 97 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 132 287 (Polychromatic418967fa.accept_15_6_12_2_1_2803 96 132
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 132 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 132 287 (accept_3_2 94 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 132 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 92 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 132 287 (accept_3_2 91 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 132 287 (Polychromatic418967fa.accept_13_12_2_1_1_2909 90 132 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 132 287
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 89 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 132 287 (accept_3_2 88 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 132 287 (Polychromatic418967fa.accept_13_9_2_1_1_813 87 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 132 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 86 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 132 287 (accept_3_2 85 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 132 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 83 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 132 287 (accept_3_2 82 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 132 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 81 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 132 287 (Polychromatic418967fa.accept_15_5_12_2_1_2820 80 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 132 287 (accept_3_2 79 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 132 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 78 132
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 132 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 132 287 (accept_3_2 76 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 132 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 132 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 74 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 132 287 (accept_3_2 73 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 132 287 (Polychromatic418967fa.accept_16_8_4_15_1_2941 72 132 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 132 287
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 71 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 132 287 (accept_3_2 70 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 132 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 69 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 132 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 68 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 132 287 (accept_3_2 67 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 132 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 132 287 (accept_3_2 64 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 132 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 132 287 (Polychromatic418967fa.accept_16_14_4_15_1_3944 62 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 132 287 (accept_3_2 61 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 132 287 (Polychromatic418967fa.accept_16_12_4_15_1_5091 60 132
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 132 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 132 287 (accept_3_2 58 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 132 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 132 287 (accept_3_2 55 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 132 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 132 287
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 53 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 132 287 (accept_3_2 52 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 132 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 132 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 287 (accept_3_2 49 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 132 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 132 287 (accept_3_2 46 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 132 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 132 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 287 (accept_3_2 43 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 287 (Polychromatic418967fa.accept_13_3_2_1_1_2907 42 132
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 132 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 132 287 (accept_3_2 40 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 132 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 287 (accept_3_2 37 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 132 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 132 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 132 287 (accept_3_2 34 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 132 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 132 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 287 (accept_3_2 31 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 132 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 132 287 (accept_3_2 28 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 132 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 132 287 (Polychromatic418967fa.accept_20_6_12_7_1_12130 26 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 287 (accept_3_2 25 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 287 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 132
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 132 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 132 287 (accept_3_2 22 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 132 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 287 (accept_3_2 19 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 287 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 132 287
  (Polychromatic418967fa.accept_20_17_12_7_1_4759 17 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 132 287 (accept_3_2 16 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 132 287 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 132 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 132 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 287 (accept_3_2 13 132 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 287 (Polychromatic418967fa.accept_9_3_6_8_1_308
  12 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 287
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 132 287 (accept_3_2 10 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  132 287 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 132 287 (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 287 (accept_3_2 7 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 287 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 132 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 132 287 (accept_3_2 4 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  132 287 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 132 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 132 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 287 (accept_3_2 1 132 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 132
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 131 287 (allA_succ_of_accept 130 131 287 (accept_3_2 130 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 129 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 129 131 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 131 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 128 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 131 287 (accept_3_2 127 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 131 287
  (Polychromatic418967fa.accept_10_6_1_7_1_342 126 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 131 287 (Polychromatic418967fa.accept_15_5_11_2_1_1095 125 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 131 287 (accept_3_2 124 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 123 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 123 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 131 287
  (Polychromatic418967fa.accept_17_3_12_15_1_1203 122 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 121 131 287 (accept_3_2 121 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 120 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 120 131 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 131 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 119 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 131 287 (accept_3_2 118 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 131 287
  (Polychromatic418967fa.accept_19_3_17_2_1_6963 117 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 131 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 116 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 131 287 (accept_3_2 115 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 114 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 131 287
  (Polychromatic418967fa.accept_21_8_5_14_1_5660 113 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 131 287 (accept_3_2 112 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 111 131 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 131 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 110 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 131 287 (accept_3_2 109 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 131 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 108 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 131 287 (Polychromatic418967fa.accept_14_9_5_7_1_1251 107 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 131 287 (accept_3_2 106 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 105 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 131 287
  (Polychromatic418967fa.accept_10_4_1_7_1_371 104 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 131 287 (accept_3_2 103 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 102 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 131 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 101 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 131 287 (accept_3_2 100 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 131 287 (Polychromatic418967fa.accept_15_9_11_2_1_1882 99 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 131 287
  (Polychromatic418967fa.accept_16_2_3_15_1_6309 98 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 131 287 (accept_3_2 97 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 131 287 (Polychromatic418967fa.accept_15_5_11_2_1_1095 95 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 131 287 (accept_3_2 94 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 131 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 92 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 131 287 (accept_3_2 91 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 131 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 131 287 (Polychromatic418967fa.accept_24_17_11_23_1_17632 89 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 131 287 (accept_3_2 88 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 87 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 131 287
  (Polychromatic418967fa.accept_10_6_1_7_1_342 86 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 131 287 (accept_3_2 85 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 131 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 131 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 131 287 (accept_3_2 82 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 131 287 (Polychromatic418967fa.accept_15_6_11_2_1_2801 81 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 80 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 131 287 (accept_3_2 79 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 131 287 (Polychromatic418967fa.accept_16_13_3_15_1_1931 77 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 287 (accept_3_2 76 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 131 287 (accept_3_2 73 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 131 287 (Polychromatic418967fa.accept_14_2_5_7_1_3767 72 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 287 (Polychromatic418967fa.accept_16_7_3_15_1_2940 71 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 287 (accept_3_2 70 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 68 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 287 (accept_3_2 67 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 287 (accept_3_2 64 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 287 (Polychromatic418967fa.accept_24_15_11_23_1_14295 63 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 287
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 62 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 287 (accept_3_2 61 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 287 (Polychromatic418967fa.accept_16_11_3_15_1_1989 59 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 287 (accept_3_2 58 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 287 (accept_3_2 55 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 287 (accept_3_2 52 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 287
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 50 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 287 (accept_3_2 49 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 287 (accept_3_2 46 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 287 (Polychromatic418967fa.accept_16_13_3_15_1_1931 45 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 44 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 287 (accept_3_2 43 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 287 (Polychromatic418967fa.accept_19_3_17_2_1_6963 41 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 287 (accept_3_2 40 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 287
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 287 (accept_3_2 37 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 287 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 287 (accept_3_2 34 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 287
  (Polychromatic418967fa.accept_21_11_5_14_1_4142 32 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 131 287 (accept_3_2 31 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 131 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 287 (accept_3_2 28 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 287
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 287 (Polychromatic418967fa.accept_10_6_1_7_1_342 26 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 287 (accept_3_2 25 131 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 287
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 23 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 287 (accept_3_2 22 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 287 (accept_3_2 19 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 287 (Polychromatic418967fa.accept_16_2_3_15_1_6309 18 131 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 287
  (Polychromatic418967fa.accept_21_17_5_14_1_4144 17 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 131 287 (accept_3_2 16 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 131 287 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 131 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 287 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 287 (accept_3_2 13 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 287
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 131 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 131 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 287 (accept_3_2 10 131 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 131 287 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 287 (Polychromatic418967fa.accept_18_8_5_17_1_1388
  8 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 287 (accept_3_2 7
  131 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 287
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 131 287 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 131 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 287 (accept_3_2 4 131 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 131 287 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 131 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 287 (Polychromatic418967fa.accept_9_2_5_8_1_11 2
  131 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 287 (accept_3_2 1 131
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 130 287 (allA_of_3_0 130 130 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 129 287
  (allA_succ_of_accept 128 129 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 128 129 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 129 287 (accept_3_2 127 129 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 126 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 129 287
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 125 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 129 287 (accept_3_2 124 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 129 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 123 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 122 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 129 287 (accept_3_2 121 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 129 287 (Polychromatic418967fa.accept_16_8_1_15_1_1982 120
  129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 129 287
  (Polychromatic418967fa.accept_9_2_3_8_1_318 119 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 129 287 (accept_3_2 118 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 129 287 (Polychromatic418967fa.accept_16_5_1_15_1_3922 117 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 116 129 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 129 287 (accept_3_2 115 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 129
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 129 287
  (Polychromatic418967fa.accept_9_5_3_8_1_316 113 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 129 287 (accept_3_2 112 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 129 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 111 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 110 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 287 (accept_3_2 109 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 129 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 108 129
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 129 287
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 107 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 129 287 (accept_3_2 106 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 129 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 105 129 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 129 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 129
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 287 (accept_3_2 103 129
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 129 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 129 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 129 287 (accept_3_2 100 129 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 129 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 129 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 129 287 (accept_3_2 97 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 129 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 96 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 129 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 287 (accept_3_2 94 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 287 (Polychromatic418967fa.accept_13_2_12_1_1_343 93 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 129 287 (accept_3_2 91 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 129 287 (Polychromatic418967fa.accept_13_11_12_1_1_2154 89 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 287 (accept_3_2 88 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 129 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 129 287 (accept_3_2 85 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 129 287 (Polychromatic418967fa.accept_19_8_15_2_1_6961 84 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 129 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 287 (accept_3_2 82 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 287 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 129 287 (accept_3_2 79 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 129 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 287 (accept_3_2 76 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 287 (accept_3_2 73 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 129 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 287 (Polychromatic418967fa.accept_15_11_9_2_1_4780 71 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 287 (accept_3_2 70 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 129 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 129 287 (accept_3_2 67 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 129 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 287 (accept_3_2 64 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 287 (accept_3_2 61 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 129 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 129 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 287 (accept_3_2 58 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 287 (Polychromatic418967fa.accept_13_5_12_1_1_2123 57 129 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 287 (accept_3_2 55 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 129 287 (Polychromatic418967fa.accept_14_11_3_7_1_604 53 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 287 (accept_3_2 52 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 129 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 287 (accept_3_2 49 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 287 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 287 (accept_3_2 46 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 287 (Polychromatic418967fa.accept_20_5_9_7_1_10766 45 129 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 287 (accept_3_2 43 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 287 (accept_3_2 40 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 287 (accept_3_2 37 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 287 (Polychromatic418967fa.accept_17_2_10_15_1_1238 36 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 287 (Polychromatic418967fa.accept_23_12_14_11_1_6189 35 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 287 (accept_3_2 34 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 129 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 287 (accept_3_2 31 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 287 (accept_3_2 28 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 287 (accept_3_2 25 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 287 (accept_3_2 22 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 287 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 129 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 287 (accept_3_2 19 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 287 (Polychromatic418967fa.accept_19_17_15_2_1_6887 17 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 287 (accept_3_2 16 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 287 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 129 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 287 (accept_3_2 13 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 287 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 287 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 287 (accept_3_2 10 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 287 (Polychromatic418967fa.accept_19_9_15_2_1_9758 9 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 287 (accept_3_2 7 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 287 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 287 (accept_3_2 4 129 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 287 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 129 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 287 (accept_3_2 1 129 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 128 287 (allA_succ_of_accept 127 128 287 (accept_3_2 127 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 126 128 287 (Polychromatic418967fa.accept_13_9_11_1_1_1375 126 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 128 287
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 125 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 128 287 (accept_3_2 124 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 123 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 128 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 122 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 128 287 (accept_3_2 121 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 128 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 120 128
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 128 287
  (Polychromatic418967fa.accept_10_9_8_7_1_714 119 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 128 287 (accept_3_2 118 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 117 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 128 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 116 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 128 287 (accept_3_2 115 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 128 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 114 128
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 128 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 113 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 128 287 (accept_3_2 112 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 111 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 128 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 110 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 128 287 (accept_3_2 109 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 128 287 (Polychromatic418967fa.accept_17_6_9_15_1_3185 108
  128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 128 287
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 107 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 128 287 (accept_3_2 106 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 128 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 128 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 128
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 128 287 (accept_3_2 103 128
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 128 287
  (Polychromatic418967fa.accept_9_3_2_8_1_108 102 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 128 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 101 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 128 287 (accept_3_2 100 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 128 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 98 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 128 287 (accept_3_2 97 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 128 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 128 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 128 287 (accept_3_2 94 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 128 287
  (Polychromatic418967fa.accept_17_7_9_15_1_8105 92 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 128 287 (accept_3_2 91 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 128 287 (Polychromatic418967fa.accept_13_12_11_1_1_2920 90 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 128 287 (Polychromatic418967fa.accept_10_9_8_7_1_714 89 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 128 287 (accept_3_2 88 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 128 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 128 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 128 287 (accept_3_2 85 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 128 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 128 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 83 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 128 287 (accept_3_2 82 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 128 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 128 287
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 80 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 128 287 (accept_3_2 79 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 128 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 128 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 128 287 (accept_3_2 76 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 128 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 128 287 (accept_3_2 73 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 128 287 (Polychromatic418967fa.accept_11_6_7_1_1_564 72 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 128 287 (Polychromatic418967fa.accept_21_8_2_14_1_10496 71 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 128 287 (accept_3_2 70 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 128 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 128 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 128 287 (accept_3_2 67 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 128 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 128 287 (Polychromatic418967fa.accept_10_5_8_7_1_2174 65 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 128 287 (accept_3_2 64 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 128 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 128 287
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 128 287 (accept_3_2 61 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 128 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 128 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 128 287 (accept_3_2 58 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 128 287
  (Polychromatic418967fa.accept_23_10_13_11_1_14504 56 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 128 287 (accept_3_2 55 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 128 287 (Polychromatic418967fa.accept_14_12_2_7_1_1243 54 128 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 287 (Polychromatic418967fa.accept_21_11_2_14_1_7225 53 128
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 287 (accept_3_2 52 128
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 287
  (Polychromatic418967fa.accept_6_3_2_5_1_32 51 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 128 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 128 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 128 287 (accept_3_2 49 128 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 128 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 128 287
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 47 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 128 287 (accept_3_2 46 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 128 287 (Polychromatic418967fa.accept_18_8_2_17_1_4782 44 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 287 (accept_3_2 43 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 128 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 128 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 128 287 (accept_3_2 40 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 128 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 38 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 287 (accept_3_2 37 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 128 287 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 128
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 287
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 35 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 287 (accept_3_2 34 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 287 (accept_3_2 31 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 287
  (Polychromatic418967fa.accept_10_9_8_7_1_714 29 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 128 287 (accept_3_2 28 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 128 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 287 (accept_3_2 25 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 128 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 128 287 (accept_3_2 22 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 128 287 (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 287 (accept_3_2 19 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 287 (Polychromatic418967fa.accept_17_1_9_15_1_3186 18 128
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 287
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 128 287 (accept_3_2 16 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 128 287 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 287 (accept_3_2 13 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 287 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 128 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 287
  (Polychromatic418967fa.accept_18_11_2_17_1_3490 11 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 128 287 (accept_3_2 10 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 287 (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 128
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 287 (accept_3_2 7 128 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 287 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 287
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 287 (accept_3_2 4 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 287 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 287 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 287 (accept_3_2 1 128 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 127 287 (allA_of_3_0 127 127 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 126 287
  (allA_succ_of_accept 125 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 125 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 126 287 (accept_3_2 124 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 126 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 123 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 126 287
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 122 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 126 287 (accept_3_2 121 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 126 287 (Polychromatic418967fa.accept_19_6_12_2_1_8379 120 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 119 126 287 7 17 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 118 126 287 (accept_3_2 118 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 117 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 117 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 126 287 (Polychromatic418967fa.accept_11_6_5_1_1_586
  116 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 126 287 (accept_3_2
  115 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 126 287
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 114 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 113 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 126 287 7 16 18 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 126 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 111 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 126 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 110 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 126 287 (accept_3_2 109 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 126 287 (Polychromatic418967fa.accept_24_12_6_23_1_7490 108 126 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 126 287
  (Polychromatic418967fa.accept_17_5_7_15_1_1230 107 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 126 287 (accept_3_2 106 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 105 126 287 7 15 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 104 126 287 (Polychromatic418967fa.accept_17_2_7_15_1_5525 104 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 126 287 (accept_3_2 103 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 126 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 102
  126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 126 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 126 287 (accept_3_2 100 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 126 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147 99 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 126 287 7 14 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 126 287 (accept_3_2 97 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 126 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 96 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 126 287 (Polychromatic418967fa.accept_22_7_16_1_1_8414 95 126
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 126 287 (accept_3_2 94 126
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9
  93 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 126 287
  (Polychromatic418967fa.accept_20_12_6_7_1_7875 92 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 91 126 287 7 13 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 90 126 287 (Polychromatic418967fa.accept_16_10_14_15_1_2933 90 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 126 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 126 287 (accept_3_2 88 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 126 287 (Polychromatic418967fa.accept_15_12_6_2_1_2760 87 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 126 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147 86 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 126 287 (accept_3_2 85 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 126 287 7 12 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 126 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188
  83 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 126 287 (accept_3_2 82
  126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 126 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 126 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 80 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 126 287 (accept_3_2 79 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 126 287 (Polychromatic418967fa.accept_22_12_16_1_1_11648 78 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 126 287 7 11 18 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 126 287 (accept_3_2 76 126 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 126 287
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 75 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 126 287 (Polychromatic418967fa.accept_16_10_14_15_1_2933 74 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 126 287 (accept_3_2 73 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 126 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 126 287
  (Polychromatic418967fa.accept_10_1_6_7_1_710 71 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 126 287 7 10 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 126 287 (Polychromatic418967fa.accept_15_8_6_2_1_1128
  68 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 287 (accept_3_2 67
  126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 126 287
  (Polychromatic418967fa.accept_19_9_12_2_1_9776 66 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 287 (accept_3_2 64 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 126 287 7 9 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 126 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 62 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 126 287 (accept_3_2 61 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 126 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 126
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 126 287
  (Polychromatic418967fa.accept_20_19_6_7_1_9289 59 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 126 287 (accept_3_2 58 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 126 287 7 8 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 126 287 (accept_3_2 55 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 126 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 54 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 126 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 287 (accept_3_2 52 126 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 287 (Polychromatic418967fa.accept_10_1_6_7_1_710
  51 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 50 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 126 287 7 7 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 126 287 (Polychromatic418967fa.accept_19_10_12_2_1_6948 48 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147
  47 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 287 (accept_3_2 46
  126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 287
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 126 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 44 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 287 (accept_3_2 43 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 126 287 7 6 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 287 (accept_3_2 40 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 287 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 126
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 287
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 126 287 (accept_3_2 37 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 126 287 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 126 287 7 5 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 126 287 (accept_3_2 34 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 287 (Polychromatic418967fa.accept_13_6_9_1_1_5604 32 126
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 287 (accept_3_2 31 126
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 287
  (Polychromatic418967fa.accept_25_5_1_12_1_17631 30 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 287 7 4 18 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 287
  (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 126 287 (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 287 (accept_3_2 25 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 126 287 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 126 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 287
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 126 287 (accept_3_2 22 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  126 287 7 3 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 126 287 (Polychromatic418967fa.accept_16_4_14_15_1_6331 20 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 126 287 (accept_3_2 19 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 126 287 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 287 (accept_3_2 16 126 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 287 (Polychromatic418967fa.accept_13_2_9_1_1_67
  15 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 287 7 2 18 41
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 287
  (accept_3_2 13 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 287
  (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 126 287 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 287 (accept_3_2 10 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 287 (Polychromatic418967fa.accept_13_8_9_1_1_2147
  8 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 126 287 7 1 18 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 126 287
  (Polychromatic418967fa.accept_11_6_5_1_1_586 6 126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 126 287 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 287 (accept_3_2 4 126 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 126 287 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 126 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 287 (Polychromatic418967fa.accept_13_2_9_1_1_67 2
  126 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 287 (accept_3_2 1 126
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  287))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 287 (allA_succ_of_accept 124 125 287 (accept_3_2 124 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 125 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 123 125 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 122 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 125 287 (accept_3_2 121 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 125 287
  (Polychromatic418967fa.accept_14_8_13_7_1_2798 120 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 125 287 (Polychromatic418967fa.accept_15_14_5_2_1_4761 119 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 125 287 (accept_3_2 118 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 125 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 117
  125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 125 287
  (Polychromatic418967fa.accept_13_12_8_1_1_825 116 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 125 287 (accept_3_2 115 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 114 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 125 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 113 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 125 287 (accept_3_2 112 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 125 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 111 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 125 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 125 287 (accept_3_2 109 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 125 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 108 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 125 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 107 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 125 287 (accept_3_2 106 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 125 287 (Polychromatic418967fa.accept_19_10_11_2_1_8354 105
  125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 125 287
  (Polychromatic418967fa.accept_14_6_13_7_1_2015 104 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 125 287 (accept_3_2 103 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 125 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 125 287 (Polychromatic418967fa.accept_15_11_5_2_1_520 101 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 125 287 (accept_3_2 100 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 125 287
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 99 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 125 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 287 (accept_3_2 97 125 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 125 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 96 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 125 287
  (Polychromatic418967fa.accept_20_15_5_7_1_4791 95 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 125 287 (accept_3_2 94 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 125 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 93 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 125 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 92 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 287 (accept_3_2 91 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 125 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 125 287
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 89 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 125 287 (accept_3_2 88 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 125 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 87 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 125 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 125 287 (accept_3_2 85 125 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 125 287 (Polychromatic418967fa.accept_13_6_8_1_1_2913 84 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 287
  (Polychromatic418967fa.accept_10_3_5_7_1_330 83 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 125 287 (accept_3_2 82 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 125 287 (Polychromatic418967fa.accept_21_18_20_14_1_5711 81 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 80 125 287 (Polychromatic418967fa.accept_19_4_11_2_1_11111 80 125 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 125 287 (accept_3_2 79 125 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 78
  125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 287
  (Polychromatic418967fa.accept_13_12_8_1_1_825 77 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 287 (accept_3_2 76 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 125 287 (Polychromatic418967fa.accept_20_15_5_7_1_4791 75 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 125 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 287 (accept_3_2 73 125 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 125 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 287
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 71 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 125 287 (accept_3_2 70 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 125 287 (Polychromatic418967fa.accept_20_9_5_7_1_6336 69 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 125 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 68 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 287 (accept_3_2 67 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 125 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 287
  (Polychromatic418967fa.accept_17_14_6_15_1_3151 65 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 125 287 (accept_3_2 64 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 125 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 125 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 125 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 287 (accept_3_2 61 125 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 287
  (Polychromatic418967fa.accept_16_12_13_15_1_1966 60 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 287 (Polychromatic418967fa.accept_13_7_8_1_1_2145 59 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 287 (accept_3_2 58 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 57 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 287
  (Polychromatic418967fa.accept_15_11_5_2_1_520 56 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 125 287 (accept_3_2 55 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 53 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 287 (accept_3_2 52 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 287 (Polychromatic418967fa.accept_13_12_8_1_1_825 51 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 287 (accept_3_2 49 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 287 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 287 (Polychromatic418967fa.accept_19_9_11_2_1_5436 47 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 287 (accept_3_2 46 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 287 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 287
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 287 (accept_3_2 43 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 287 (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 287 (accept_3_2 40 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 287 (Polychromatic418967fa.accept_21_18_20_14_1_5711 39
  125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 287 (accept_3_2 37 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 287 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 35 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 287 (accept_3_2 34 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 33 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 287
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 287 (accept_3_2 31 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 287 (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 287 (accept_3_2 28 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 287 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 287 (accept_3_2 25 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 287 (accept_3_2 22 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 287 (Polychromatic418967fa.accept_23_21_10_11_1_17630 21
  125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 287
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 20 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 287 (accept_3_2 19 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 287 (Polychromatic418967fa.accept_21_17_20_14_1_11808 17 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 287 (accept_3_2 16 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 287 (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 125
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 287 (accept_3_2 13 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 287 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 287 (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 287 (accept_3_2 10 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 287 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 125 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 287
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 287 (accept_3_2 7 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 287 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 287 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 125 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 287 (accept_3_2 4 125 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 287 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 125 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 287
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 287 (accept_3_2 1 125 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 124 287 (allA_of_3_0 124 124 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 123 287
  (allA_succ_of_accept 122 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 122 123 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 123 287 (accept_3_2 121 123 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 120 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 123 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 119 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 123 287 (accept_3_2 118 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 123 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 117 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 116 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 116 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 123 287 (accept_3_2 115 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 114 123
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 123 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 113 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 123 287 (accept_3_2 112 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 111 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 110 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 287 (accept_3_2 109 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 108 123
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 123 287
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 107 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 123 287 (accept_3_2 106 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 123 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 105 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 287 (accept_3_2 103 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 102 123
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 101 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 123 287 (accept_3_2 100 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 123 287 (Polychromatic418967fa.accept_13_8_6_1_1_3808 99 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 98 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 287 (accept_3_2 97 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 96 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 95 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 123 287 (accept_3_2 94 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 287 (accept_3_2 91 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 287 (Polychromatic418967fa.accept_16_10_11_15_1_6302 90 123 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 287
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 89 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 287 (accept_3_2 88 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 123 287 (Polychromatic418967fa.accept_11_10_2_1_1_1036 87 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 287 (accept_3_2 85 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 83 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 123 287 41 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 123 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 123 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 123 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 287 (accept_3_2 79 123 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 287
  (Polychromatic418967fa.accept_17_10_4_15_1_2165 78 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 123 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 287 (accept_3_2 76 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 123 287 (accept_3_2 73 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 123 287 (Polychromatic418967fa.accept_13_7_6_1_1_368 72 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 123 287 (Polychromatic418967fa.accept_16_7_11_15_1_2929 71 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 287 (accept_3_2 70 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 123 287 (Polychromatic418967fa.accept_11_3_2_1_1_994 69 123
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 123 287 (accept_3_2 67 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 123 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 287 (accept_3_2 64 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 123 287 (Polychromatic418967fa.accept_18_9_15_17_1_3497 63 123 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 123 287 (accept_3_2 61 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 123 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 123 287 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 287 (accept_3_2 58 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 123 287 (accept_3_2 55 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 123 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 123 287 (Polychromatic418967fa.accept_17_2_4_15_1_5451 53 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 287 (accept_3_2 52 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 123 287 (Polychromatic418967fa.accept_16_3_11_15_1_1963 51 123
  287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 123 287 (accept_3_2 49 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 123 287 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 287 (accept_3_2 46 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 287
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 123 287 (accept_3_2 43 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 123 287 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 41 123 287 41 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 40 123 287 (accept_3_2 40 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 123 287 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 123 287
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 287 (accept_3_2 37 123 287
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 287 (Polychromatic418967fa.accept_8_4_3_7_1_491
  36 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 287
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 287 (accept_3_2 34 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 287 (accept_3_2 31 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 287 (accept_3_2 28 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 287 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 287 (accept_3_2 25 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 287 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 287 (accept_3_2 22 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 287 (accept_3_2 19 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 287 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 287
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 287 (accept_3_2 16 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 287 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 287 (accept_3_2 13 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 287 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 287
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 287 (accept_3_2 10 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 287 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 287 (accept_3_2 7 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 287 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 123 287 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 287
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 287 (accept_3_2 4 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 287 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 123 287 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 287 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 287 (accept_3_2 1 123 287 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123
  287)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_287_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))


