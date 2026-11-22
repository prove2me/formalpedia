-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch255_Segment000
-- name    : Polychromatic418967fa_Branch255_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:39:51.724701+00:00
-- url     : https://prove2.me/theorems/befd345d-e927-4339-83fa-bc173b8d5dc0
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

def Polychromatic418967fa.branch_255_segment_000 : allB 100 255 :=
  allB_succ 99 255 (allA_succ_of_accept 98 99 255 (Polychromatic418967fa.accept_16_2_3_15_1_6309 98 99 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 255
  (Polychromatic418967fa.accept_18_7_9_3_1_800 97 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 255 3 32 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 95 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 94 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 255 3 31 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 92 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 91 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 255 3 30 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 89
  99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 88 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 255 3 29 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 86 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 255 (Polychromatic418967fa.accept_18_13_9_3_1_5114 85 99
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 255 3 28 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 255
  (Polychromatic418967fa.accept_22_17_11_13_1_13932 83 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 99 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 99 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 255 3 27 33 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 255
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 80 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 99 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 99 255 3 26 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 99 255 (Polychromatic418967fa.accept_16_13_3_15_1_1931
  77 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 76 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 99 255 3 25 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 99 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 74 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 99 255 (Polychromatic418967fa.accept_18_1_9_3_1_2672 73 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 255 3 24 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 71 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 99 255 (Polychromatic418967fa.accept_19_13_4_8_1_11571 70 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 99 255 3 23 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 99 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 68
  99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 99 255 3 22 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 99 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 64 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 255 3 21 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 255
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 62 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 99 255 3 20 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 99 255 (Polychromatic418967fa.accept_16_11_3_15_1_1989
  59 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 58 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 99 255 3 19 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 99 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 56 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 255 (Polychromatic418967fa.accept_16_7_3_15_1_2940 55 99
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 255 3 18 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 99 255 3 17 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 99 255 (Polychromatic418967fa.accept_16_2_3_15_1_6309
  50 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 255
  (Polychromatic418967fa.accept_18_13_9_3_1_5114 49 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 99 255 3 16 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 99 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 255 3 15 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 255 (Polychromatic418967fa.accept_16_11_3_15_1_1989 43 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 99 255 3 14 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 99 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 41
  99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 40 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 99 255 3 13 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 99 255 (Polychromatic418967fa.accept_18_2_9_3_1_3825 38 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 255 3 12 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 255
  (Polychromatic418967fa.accept_21_14_15_3_1_9580 35 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 34 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 255 3 11 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 32
  99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 31 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 99 255 3 10 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 99 255 (Polychromatic418967fa.accept_16_13_3_15_1_1931 29 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 255 3 9 33 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 255 3 8 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 255
  (Polychromatic418967fa.accept_19_3_4_8_1_8808 22 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 99 255 3 7 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 99 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 255 3 6 33 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 255
  (Polychromatic418967fa.accept_19_17_4_8_1_4500 17 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 255 3 5 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 255
  (Polychromatic418967fa.accept_16_13_3_15_1_1931 13 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 99 255 3 4 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 99 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 255 (Polychromatic418967fa.accept_19_10_4_8_1_11500 10 99
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 255 3 3 33 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 255
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 8 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 255 (Polychromatic418967fa.accept_16_7_3_15_1_2940 7 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 255 3 2 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 99 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 99 255 3 1 33 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 99 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 99 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 99 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  255 (allA_succ_of_accept 97 98 255 (accept_3_4 97 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 96 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 95 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 255 (accept_3_4 94 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 92 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 255 (accept_3_4 91 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 90 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 255 (accept_3_4 88 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 86 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 255 (accept_3_4 85 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 255 (Polychromatic418967fa.accept_18_12_8_3_1_1627 84 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 255 (accept_3_4 82 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 255
  (Polychromatic418967fa.accept_13_2_7_8_1_4221 80 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 255 (accept_3_4 79 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 255 (accept_3_4 76 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 255 (Polychromatic418967fa.accept_13_10_7_8_1_1794 75 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 74 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 255 (accept_3_4 73 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 255 (accept_3_4 70 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 68 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 255 (accept_3_4 67 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 255 (accept_3_4 64 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 255
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 255 (accept_3_4 61 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 255 (accept_3_4 58 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 255 (accept_3_4 55 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 255 (accept_3_4 52 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 255 (accept_3_4 49 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 255 (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 255 (accept_3_4 46 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 255
  (Polychromatic418967fa.accept_16_12_2_15_1_490 44 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 255 (accept_3_4 43 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 255 (accept_3_4 40 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 255 (Polychromatic418967fa.accept_26_13_20_21_1_15568 39 98 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 255 (accept_3_4 37 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 255 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 255 (accept_3_4 34 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 255 (accept_3_4 31 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 255 (accept_3_4 28 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 255
  (Polychromatic418967fa.accept_23_3_6_2_1_15567 26 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 255 (accept_3_4 25 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 255 (accept_3_4 22 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 255 (accept_3_4 19 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 255 (accept_3_4 16 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 255 (accept_3_4 13 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 255 (accept_3_4 10 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 255
  (Polychromatic418967fa.accept_21_8_14_3_1_9602 8 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 255 (accept_3_4 7 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 255 (accept_3_4 4 98 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 98 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  98 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 255 (accept_3_4 1 98 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  255 (allA_succ_of_accept 96 97 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 96 97 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 255 (accept_3_5 95 97 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 93
  97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 255 (accept_3_5 92 97
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 255 (Polychromatic418967fa.accept_9_1_7_3_1_41
  91 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 255 (accept_3_5 89 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 87 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 255 (accept_3_5 86 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 85 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 255
  (Polychromatic418967fa.accept_11_7_9_2_1_260 84 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 255 (accept_3_5 83 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 255 (accept_3_5 80 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 255 (accept_3_5 77 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 255 (Polychromatic418967fa.accept_16_11_1_15_1_1123 75 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 255 (accept_3_5 74 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 97 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 255 (accept_3_5 71 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 255 (accept_3_5 68 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 255 (accept_3_5 65 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 255 (accept_3_5 62 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 255 (Polychromatic418967fa.accept_37_24_23_33_1_15566 61 97 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 255 (accept_3_5 59 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 255 (accept_3_5 56 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 255 (accept_3_5 53 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 255 (accept_3_5 50 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 255
  (Polychromatic418967fa.accept_10_8_7_5_1_602 48 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 255 (accept_3_5 47 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 255 (accept_3_5 44 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 255 (accept_3_5 41 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 255 (accept_3_5 38 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 255
  (Polychromatic418967fa.accept_24_12_1_15_1_12071 36 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 97 255 (accept_3_5 35 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 97 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 97 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 255 (accept_3_5 32 97 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31
  97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 255 (accept_3_5 29 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 255 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 255 (accept_3_5 26 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 255 (accept_3_5 23 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 255 (accept_3_5 20 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 255 (accept_3_5 17 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 255 (accept_3_5 14 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 255
  (Polychromatic418967fa.accept_10_2_7_5_1_605 12 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 255 (accept_3_5 11 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 255 (accept_3_5 8 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 97 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 255 (accept_3_5 5 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 97 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 255 (accept_3_5 2 97 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 97 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 255
  (allA_succ_of_accept 95 96 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 95 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 94 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 96 255 3 31 32 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 96 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 92 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 96 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 91 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 255 3 30 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 89
  96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 96 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 88 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 96 255 3 29 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 96 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 86 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 255 3 28 32 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 82 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 255 3 27 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 80
  96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 79 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 255 3 26 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 96 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 96 255 3 25 32 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 96 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 74 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 96 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 255 3 24 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 71
  96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 70 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 96 255 3 23 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 96 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 255 3 22 32 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 255 3 21 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 255 3 20 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 96 255 3 19 32 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 96 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 96 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 255 3 18 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 53
  96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 96 255 3 17 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 96 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 255 3 16 32 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 255 3 15 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 44
  96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 255 3 14 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 255 3 13 32 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 255 3 12 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 96 255 3 11 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 96 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 255 3 10 32 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 255 3 9 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 255 3 8 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 255 3 7 32 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 255 3 6 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 96 255 3 5 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 96 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 255 3 4 32 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 255 3 3 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 255 3 2 32 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 96 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 255 3 1 32 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 96 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 255
  (allA_succ_of_accept 94 95 255 (accept_3_4 94 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 93 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 255 (accept_3_4 91 95 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 90 95 255 5 18 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 95 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 89 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 95 255 (accept_3_4 88 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 95 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 87
  95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 95 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 86 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 95 255 5 17 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 95 255 (Polychromatic418967fa.accept_22_18_7_13_1_10819 84 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 95 255 (accept_3_4 82 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 95 255 (Polychromatic418967fa.accept_12_9_11_3_1_772
  81 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 95 255 5 16 19 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 95 255 (accept_3_4 79
  95 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 95 255 (Polychromatic418967fa.accept_13_12_4_8_1_1120 77 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 95 255 (accept_3_4 76 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 95 255 5 15 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 95 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 95 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 255 (accept_3_4 73 95 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 255 (Polychromatic418967fa.accept_22_6_7_13_1_15565 72 95
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 95 255 5 14 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 95 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 255 (accept_3_4 67 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 255 (Polychromatic418967fa.accept_23_20_3_2_1_5458
  66 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 95 255 5 13 19 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 95 255 (accept_3_4 64
  95 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 255
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 63 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 95 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 255 (accept_3_4 61 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 95 255 5 12 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 95 255 (Polychromatic418967fa.accept_22_15_7_13_1_15564 59 95 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 255 (accept_3_4 58 95 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 95 255 5 11 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 95 255 (Polychromatic418967fa.accept_21_12_11_3_1_1052 54 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 255 (accept_3_4 52 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 51
  95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 95 255 5 10 19 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 95 255 (accept_3_4 49
  95 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 95 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 255 (accept_3_4 46 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 95 255 5 9 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 95 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 255 (accept_3_4 43 95 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 95 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 95 255 5 8 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 95 255 (Polychromatic418967fa.accept_21_18_11_3_1_8042 39 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 255 (accept_3_4 37 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36
  95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 255 5 7 19 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 255 (accept_3_4 34
  95 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 95 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 255 (accept_3_4 31 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 95 255 5 6 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 95 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 95 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 255 (accept_3_4 28 95 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 95 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 95 255 5 5 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 95 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 255 (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 95
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 255 (accept_3_4 22 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 255 (Polychromatic418967fa.accept_12_9_11_3_1_772
  21 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 255 5 4 19 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 255 (accept_3_4 19
  95 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 255
  (Polychromatic418967fa.accept_21_18_11_3_1_8042 18 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 95 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 255 (accept_3_4 16 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 95 255 5 3 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 95 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 95 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 255 (accept_3_4 13 95 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 255 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 95 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 95 255 5 2 19 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 95 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 255 (accept_3_4 7 95 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 255 5 1 19 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 255 (accept_3_4 4 95
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 255
  (Polychromatic418967fa.accept_25_3_20_5_1_15563 3 95 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 255 (accept_3_4 1 95 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 255
  (allA_succ_of_accept 93 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 255 (accept_3_5 92 94 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  90 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 255 (accept_3_5 89
  94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 255
  (Polychromatic418967fa.accept_9_7_4_3_1_204 88 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 87 94 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 255 (accept_3_5 86 94 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 255
  (Polychromatic418967fa.accept_16_4_14_15_1_6331 84 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 94 255 (accept_3_5 83 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  94 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 82 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 94 255 (accept_3_5 80 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 94 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 94 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 78 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 94 255 (accept_3_5 77 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  94 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 76 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 94 255 (Polychromatic418967fa.accept_21_12_10_3_1_11112 75 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 255 (accept_3_5 74 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 255
  (Polychromatic418967fa.accept_13_7_3_8_1_1750 72 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 94 255 (accept_3_5 71 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  94 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 255 (accept_3_5 68 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 94 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 255
  (Polychromatic418967fa.accept_10_6_4_5_1_615 66 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 94 255 (accept_3_5 65 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  94 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 94 255 (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 255 (accept_3_5 62 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 94 255 (accept_3_5 59 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  94 255 (Polychromatic418967fa.accept_16_10_14_15_1_2933 58 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 94 255 (accept_3_5 56 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 94 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 94 255 (accept_3_5 53 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  94 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 94 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 255 (accept_3_5 50 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 255
  (Polychromatic418967fa.accept_11_4_6_2_1_51 48 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 94 255 (accept_3_5 47 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  94 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 255 (accept_3_5 44 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 255 (accept_3_5 41 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 255 (Polychromatic418967fa.accept_22_18_6_13_1_7751 40 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 255 (accept_3_5 38 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 255
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 255 (accept_3_5 35 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 255 (accept_3_5 32 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 255 (accept_3_5 29 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 255 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 255 (accept_3_5 26 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 255 (accept_3_5 23 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 255 (Polychromatic418967fa.accept_13_9_3_8_1_573 22 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 255 (accept_3_5 20 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 255 (accept_3_5 17 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 255 (accept_3_5 14 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 255
  (Polychromatic418967fa.accept_21_12_10_3_1_11112 12 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 94 255 (accept_3_5 11 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 94 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 94 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 255 (accept_3_5 8 94 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 94
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 255 (accept_3_5 5 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  255 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 94 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 94 255 (Polychromatic418967fa.accept_24_3_22_15_1_1938 3 94 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 255 (accept_3_5 2 94 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 94 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 255
  (allA_succ_of_accept 92 93 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 92 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 91 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 255 3 30 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 89 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 88 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 255 3 29 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 86
  93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 85 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 255 3 28 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 255 3 27 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 255
  (Polychromatic418967fa.accept_19_4_17_8_1_2103 80 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 79 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 255 3 26 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 77
  93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 76 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 255 3 25 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 73 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 255 3 24 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 255 3 23 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 68
  93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 67 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 255 3 22 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 255 3 21 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 255 3 20 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 255 (Polychromatic418967fa.accept_12_11_9_3_1_792
  59 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 255 3 19 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 255 (Polychromatic418967fa.accept_21_14_9_3_1_4893 56 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 255 3 18 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 53 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 255 3 17 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 255 3 16 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 255 3 15 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 255
  (Polychromatic418967fa.accept_16_12_13_15_1_1966 44 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 93 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 93 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 255 3 14 31 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 255 3 13 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 37 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 93 255 3 12 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 93 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 255 3 11 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 255
  (Polychromatic418967fa.accept_10_2_3_5_1_996 32 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 255 3 10 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 255
  (Polychromatic418967fa.accept_10_8_3_5_1_613 28 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 93 255 3 9 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 255 3 8 31 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 255 3 7 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 93 255 3 6 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 93 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 255 (Polychromatic418967fa.accept_19_16_17_8_1_8762 16 93
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 255 3 5 31 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 255 3 4 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 93 255 3 3 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 93 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 255 3 2 31 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 255 (Polychromatic418967fa.accept_19_4_17_8_1_2103 4 93 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 255 3 1 31 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 93 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 92 255 (allA_succ_of_accept 91 92 255 (accept_3_4 91 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 92 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 90 92 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 255 (accept_3_4 88 92 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 87
  92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 255 (accept_3_4 85 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 255 (Polychromatic418967fa.accept_13_6_1_8_1_1116 84 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 255 (accept_3_4 82 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 80 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 255 (accept_3_4 79 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 255 (accept_3_4 76 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 255 (accept_3_4 73 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 255 (accept_3_4 70 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 255 (accept_3_4 67 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 255 (accept_3_4 64 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 62 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 255 (accept_3_4 61 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 255 (accept_3_4 58 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 255
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 56 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 255 (accept_3_4 55 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 255 (accept_3_4 52 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 255 (accept_3_4 49 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 255 (accept_3_4 46 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 255 (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 255 (accept_3_4 43 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 255 (accept_3_4 40 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 255 (accept_3_4 37 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 255 (Polychromatic418967fa.accept_16_4_12_15_1_6289 36 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 255 (accept_3_4 34 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 255 (accept_3_4 31 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 255 (accept_3_4 28 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 255 (accept_3_4 25 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 255 (accept_3_4 22 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 255 (Polychromatic418967fa.accept_30_21_2_15_1_15562 21 92 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 255
  (Polychromatic418967fa.accept_11_9_4_2_1_600 20 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 255 (accept_3_4 19 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 255 (accept_3_4 16 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 255 (accept_3_4 13 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 255 (accept_3_4 10 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 92 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 255 (accept_3_4 7 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 255 (accept_3_4 4 92 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 92 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  92 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 255 (accept_3_4 1 92 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 255
  (allA_succ_of_accept 90 91 255 (Polychromatic418967fa.accept_16_10_11_15_1_6302 90 91 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 255 (accept_3_5 89 91 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 87
  91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 255 (accept_3_5 86 91
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 85 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 91 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 255 (accept_3_5 83 91 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  81 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 255 (accept_3_5 80
  91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 255
  (Polychromatic418967fa.accept_9_7_1_3_1_443 79 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 91 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 78 91 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 255 (accept_3_5 77 91 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 255 (Polychromatic418967fa.accept_21_12_7_3_1_4927
  75 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 255 (accept_3_5 74
  91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 255
  (Polychromatic418967fa.accept_19_16_15_8_1_10086 73 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 91 255 (Polychromatic418967fa.accept_21_9_7_3_1_4888 72 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 255 (accept_3_5 71 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 91 255 (accept_3_5 68 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  91 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 91 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 66 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 255 (accept_3_5 65 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 255
  (Polychromatic418967fa.accept_18_9_1_3_1_6451 63 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 255 (accept_3_5 62 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 255 (accept_3_5 59 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 255 (accept_3_5 56 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 255 (Polychromatic418967fa.accept_16_7_11_15_1_2929 55 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 255 (accept_3_5 53 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 255 (accept_3_5 50 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 255 (Polychromatic418967fa.accept_18_12_1_3_1_7843 48 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 255 (accept_3_5 47 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 91 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 255
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 255 (accept_3_5 44 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 255 (accept_3_5 41 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 39 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 255 (accept_3_5 38 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 255 (Polychromatic418967fa.accept_21_16_7_3_1_8093 37 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 255 (accept_3_5 35 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 255 (accept_3_5 32 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 255 (Polychromatic418967fa.accept_18_12_1_3_1_7843 30 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 255 (accept_3_5 29 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 255
  (Polychromatic418967fa.accept_18_9_1_3_1_6451 27 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 255 (accept_3_5 26 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 255 (accept_3_5 23 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 255 (accept_3_5 20 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 255 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 255 (accept_3_5 17 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 255 (accept_3_5 14 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 255 (accept_3_5 11 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 91 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 255 (accept_3_5 8 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 91 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 255 (accept_3_5 5 91 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 255 (Polychromatic418967fa.accept_16_3_11_15_1_1963
  3 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 255 (accept_3_5 2 91
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 255
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 91 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 91 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  90 255 (allA_succ_of_accept 89 90 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 255 3 29 30 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 86 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 85 90 255 5 17 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 90 255 3 28 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 255 (Polychromatic418967fa.accept_13_5_12_8_1_198 83 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 82 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 90 255 3 27 30 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 90 255 5 16 18 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 90 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 90 255 3 26 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 90 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 90 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 76 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 255 15 5 6 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 74 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 90 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 255 3 24 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 255
  (Polychromatic418967fa.accept_20_11_10_15_1_11318 71 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 90 255 5 14 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 90 255 3 23 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 90 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 68 90 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 255 3 22 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 90 255 5 13 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 90 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 64 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 90 255 3 21 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 90 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 62
  90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 255 15 4 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 90 255 (Polychromatic418967fa.accept_13_7_12_8_1_199 59 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 90 255 3 19 30 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 90 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 90 255 5 11 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 90 255 3 18 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 90 255 3 17 30 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 90 255 5 10 18 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 255 3 16 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 90 255 (Polychromatic418967fa.accept_19_9_14_8_1_11549 47 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 90 255 15 3 6 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 90 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 90 255 (Polychromatic418967fa.accept_13_4_12_8_1_197 43 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 255 3 14 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 255 5 8 18 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 90 255 3 13 30 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 90 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 255 3 12 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 255 5 7 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 90 255 (Polychromatic418967fa.accept_12_10_6_3_1_786
  34 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 255 3 11 30 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 255 (Polychromatic418967fa.accept_13_5_12_8_1_198 31 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 255 15 2 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 90 255 3 9 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 90 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 90 255 5 5 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 255 3 8 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 90 255 3 7 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 90 255 5 4 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 255 (Polychromatic418967fa.accept_20_19_10_15_1_1529 19 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 255 3 6 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 90 255 15 1 6 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 90 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 255 3 4 30 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 255 5 2 18 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 90 255 3 3 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 255 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 255 3 2 30 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 255 5 1 18 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 90 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 90 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 90 255 3 1 30 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 90 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 90 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 255
  (allA_succ_of_accept 88 89 255 (accept_3_4 88 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 255 (accept_3_4 85 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 83 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 255 (accept_3_4 82 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 255 (accept_3_4 79 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 77 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 255 (accept_3_4 76 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 255 (Polychromatic418967fa.accept_13_10_11_8_1_1770 75 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 255 (accept_3_4 73 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 255 (accept_3_4 70 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 255 (accept_3_4 67 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 255 (accept_3_4 64 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 255 (Polychromatic418967fa.accept_19_6_13_8_1_4508 63 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 255 (accept_3_4 61 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 59 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 255 (accept_3_4 58 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 255 (accept_3_4 55 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 255
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 53 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 255 (accept_3_4 52 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 255 (accept_3_4 49 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 48 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 47 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 255 (accept_3_4 46 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 255 (accept_3_4 43 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 255 (accept_3_4 40 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 255 (Polychromatic418967fa.accept_19_1_13_8_1_8779 39 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 255 (accept_3_4 37 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 255
  (Polychromatic418967fa.accept_13_9_11_8_1_195 35 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 255 (accept_3_4 34 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 255 (accept_3_4 31 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 255 (accept_3_4 28 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 255 (accept_3_4 25 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 255 (accept_3_4 22 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 255 (accept_3_4 19 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 255
  (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 255 (accept_3_4 16 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 255 (accept_3_4 13 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 255 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 255 (accept_3_4 10 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 255 (accept_3_4 7 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 255 (accept_3_4 4 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 89 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 255 (accept_3_4 1 89 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 255
  (allA_succ_of_accept 87 88 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 87 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 255 (accept_3_5 86 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 255 (Polychromatic418967fa.accept_16_4_8_15_1_1113
  84 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 255 (accept_3_5 83
  88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 255
  (Polychromatic418967fa.accept_9_1_7_3_1_41 82 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 88 255 (Polychromatic418967fa.accept_16_1_8_15_1_1945 81 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 255 (accept_3_5 80 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 78
  88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 255 (accept_3_5 77 88
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 76 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 88 255 (Polychromatic418967fa.accept_21_12_4_3_1_4924 75 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 255 (accept_3_5 74 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 255 (Polychromatic418967fa.accept_10_2_8_5_1_587
  72 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 255 (accept_3_5 71
  88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 255
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 70 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 88 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 255 (accept_3_5 68 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 255 (Polychromatic418967fa.accept_12_6_4_3_1_361
  66 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 255 (accept_3_5 65
  88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 64 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 88 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 255 (accept_3_5 62 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 60
  88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 255 (accept_3_5 59 88
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 255 (Polychromatic418967fa.accept_9_4_7_3_1_43
  58 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 255 (accept_3_5 56 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 255 (accept_3_5 53 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 52 88 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 255 (accept_3_5 50 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 255 (accept_3_5 47 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 88 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 255
  (Polychromatic418967fa.accept_19_7_12_8_1_10122 45 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 255 (accept_3_5 44 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 255 (accept_3_5 41 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 88 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 255
  (Polychromatic418967fa.accept_16_7_8_15_1_6327 39 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 255 (accept_3_5 38 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 255 (accept_3_5 35 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 88 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 255 (accept_3_5 32 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 255 (accept_3_5 29 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 88 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 255 (accept_3_5 26 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 255 (accept_3_5 23 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 88 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 255
  (Polychromatic418967fa.accept_14_7_4_3_1_488 21 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 255 (accept_3_5 20 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 255 (accept_3_5 17 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 255 (Polychromatic418967fa.accept_25_16_13_5_1_4699 16 88 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 255 (accept_3_5 14 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 255 (accept_3_5 11 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 88 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 255
  (Polychromatic418967fa.accept_16_9_8_15_1_5095 9 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 255 (accept_3_5 8 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 88 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 255 (accept_3_5 5 88 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 88 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 88 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3
  88 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 255 (accept_3_5 2 88 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 255
  (allA_succ_of_accept 86 87 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 86 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 85 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 255 3 28 29 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 82 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 255 3 27 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 80
  87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 79 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 255 3 26 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 255 3 25 29 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 74 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 255 3 24 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 71
  87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 70 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 255 3 23 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 255 3 22 29 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 255 3 21 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 255 3 20 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 255 3 19 29 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 255 3 18 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 53
  87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 255 3 17 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 255 3 16 29 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 255 3 15 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 44
  87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 255 3 14 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 255 3 13 29 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 255 3 12 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 255 3 11 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 255 3 10 29 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 255 3 9 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 255 3 8 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 255 3 7 29 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 255 3 6 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 255 3 5 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 255 3 4 29 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 255 3 3 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 255 3 2 29 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 87 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 255 3 1 29 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 87 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 87 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 255
  (allA_succ_of_accept 85 86 255 (accept_3_4 85 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 84 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 255 (accept_3_4 82 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 80 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 255 (accept_3_4 79 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 255 (accept_3_4 76 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 74 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 255 (accept_3_4 73 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 255 (Polychromatic418967fa.accept_20_12_6_15_1_6845 72 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 255 (accept_3_4 70 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 255 (accept_3_4 67 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 255 (accept_3_4 64 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 255 (Polychromatic418967fa.accept_18_9_14_3_1_6407 63 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 255 (accept_3_4 61 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 255 (accept_3_4 58 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 255 (accept_3_4 55 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 255 (accept_3_4 52 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 255 (accept_3_4 49 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 255 (accept_3_4 46 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 44 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 255 (accept_3_4 43 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 255 (accept_3_4 40 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 255 (accept_3_4 37 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 255 (accept_3_4 34 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 255
  (Polychromatic418967fa.accept_20_12_6_15_1_6845 32 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 255 (accept_3_4 31 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 255 (accept_3_4 28 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 255 (accept_3_4 25 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 255 (accept_3_4 22 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 255 (accept_3_4 19 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 255 (accept_3_4 16 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 255 (accept_3_4 13 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 255 (accept_3_4 10 86 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 255 (accept_3_4 7 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 255 (accept_3_4 4 86 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 255 (Polychromatic418967fa.accept_24_3_14_15_1_12115 3 86 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 86 255 (accept_3_4 1 86 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 255
  (allA_succ_of_accept 84 85 255 (Polychromatic418967fa.accept_16_4_5_15_1_5083 84 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 255 (accept_3_5 83 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 81
  85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 85 255 5 16 17 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 85 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 79 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 255 (accept_3_5 77 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 85 255 5 15 17 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 85 255 (accept_3_5 74 85 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 255 (accept_3_5 71 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 85
  255 5 14 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  85 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 85 255 17 4 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 85 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 85 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 85 255 5 13 17 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 85 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 85 255 (Polychromatic418967fa.accept_18_9_13_3_1_5088 63 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 255 (accept_3_5 62 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 85 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 85 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 85 255 5 12 17 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 85 255 (accept_3_5 59 85 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 57 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 255 (accept_3_5 56 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 85
  255 5 11 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  85 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 85 255 (accept_3_5 53 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 85 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 85 255 17 3 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 85 255 5 10 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 85 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 255
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 255 (accept_3_5 47 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 85 255 5 9 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 85 255 (accept_3_5 44 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 85 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 255 (accept_3_5 41 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 85 255 5 8 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 85 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39
  85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 255 (accept_3_5 38 85
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 85 255 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 85 255 5 7 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 85 255 17 2 5 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 85 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 255 (accept_3_5 32 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 255
  (Polychromatic418967fa.accept_20_11_5_15_1_8438 31 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 85 255 5 6 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 85 255 (accept_3_5 29 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 85 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 255 (accept_3_5 26 85 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 85 255 5 5 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 85 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 85 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 255 (accept_3_5 23 85 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 255
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 85 255 5 4 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 85 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 85 255 17 1 5 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 85 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 85 255 5 3 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 85 255 (accept_3_5 14 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 255 (Polychromatic418967fa.accept_20_13_5_15_1_8431 13 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 255 (accept_3_5 11 85 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 85 255 5 2 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 85 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 85 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 255 (accept_3_5 8 85 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 85 255 5 1 17 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 85 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 255 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 255 (accept_3_5 2 85 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  85 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 255
  (allA_succ_of_accept 83 84 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 255 (Polychromatic418967fa.accept_20_2_4_15_1_6911 82 84
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 255 3 27 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 255
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 80 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 79 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 255 3 26 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 255 (Polychromatic418967fa.accept_23_8_15_2_1_15561
  77 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 84 255
  (Polychromatic418967fa.accept_10_6_4_5_1_615 76 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 84 255 3 25 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 84 255 (Polychromatic418967fa.accept_18_2_12_3_1_2707 74 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 255 (Polychromatic418967fa.accept_18_1_12_3_1_6426 73 84
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 255 3 24 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 255
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 71 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 255 (Polychromatic418967fa.accept_20_10_4_15_1_12657 70 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 255 3 23 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 255 (Polychromatic418967fa.accept_18_14_12_3_1_5103
  68 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 67 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 255 3 22 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 255 (Polychromatic418967fa.accept_20_5_4_15_1_3931 65 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 84 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84 255 3 21 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 84 255
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 62 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 84 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 61 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 255 3 20 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 59
  84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 255
  (Polychromatic418967fa.accept_22_14_18_13_1_10864 58 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 57 84 255 3 19 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 84 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 56 84 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 255
  (Polychromatic418967fa.accept_18_1_12_3_1_6426 55 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 84 255 3 18 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 84 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 53 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 255 (Polychromatic418967fa.accept_25_2_9_5_1_15560 52 84
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 255 3 17 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 255
  (Polychromatic418967fa.accept_13_11_6_8_1_1121 50 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 84 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 255 3 16 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 255
  (Polychromatic418967fa.accept_27_20_3_12_1_15559 47 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 84 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 84 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 255 3 15 28 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 255
  (Polychromatic418967fa.accept_16_12_4_15_1_5091 44 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 255 3 14 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031
  41 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 255
  (Polychromatic418967fa.accept_13_1_6_8_1_208 40 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 84 255 3 13 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 84 255 (Polychromatic418967fa.accept_18_2_12_3_1_2707 38 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 255 (Polychromatic418967fa.accept_13_11_6_8_1_1121 37 84
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 255 3 12 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 255 (Polychromatic418967fa.accept_26_8_6_21_1_15558 34 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 255 3 11 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 255 (Polychromatic418967fa.accept_18_14_12_3_1_5103
  32 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 255
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 255 3 10 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 29 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 255 (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 84 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 255 3 9 28 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 255
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 255 (Polychromatic418967fa.accept_18_7_12_3_1_804 25 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 255 3 8 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 255 (Polychromatic418967fa.accept_22_1_18_13_1_10865 23 84
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 255
  (Polychromatic418967fa.accept_20_2_4_15_1_6911 22 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 84 255 3 7 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 84 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 84 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 255 3 6 28 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 255
  (Polychromatic418967fa.accept_22_17_18_13_1_4404 17 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 84 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 84 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 255 3 5 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 255 (Polychromatic418967fa.accept_13_1_6_8_1_208 14
  84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 255
  (Polychromatic418967fa.accept_18_13_12_3_1_3857 13 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 255 3 4 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 255 (Polychromatic418967fa.accept_20_10_4_15_1_12657 10 84
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 255 3 3 28 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 255
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 255 (Polychromatic418967fa.accept_18_7_12_3_1_804 7 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 255 3 2 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 255 (Polychromatic418967fa.accept_16_5_4_15_1_1102 5 84 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 255
  (Polychromatic418967fa.accept_23_4_15_2_1_15557 4 84 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 84 255 3 1 28 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 84 255 (Polychromatic418967fa.accept_13_2_6_8_1_1092 2 84 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 84 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 255
  (allA_succ_of_accept 82 83 255 (accept_3_4 82 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 255 (accept_3_4 79 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 255 (accept_3_4 76 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 255 (Polychromatic418967fa.accept_13_10_5_8_1_2555 75 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 255 (accept_3_4 73 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 71 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 255 (accept_3_4 70 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 255 (accept_3_4 67 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 255 (Polychromatic418967fa.accept_13_1_5_8_1_207 66 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 255 (accept_3_4 64 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 255 (Polychromatic418967fa.accept_19_6_7_8_1_10108 63 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 255 (accept_3_4 61 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 255 (accept_3_4 58 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 255 (accept_3_4 55 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 255 (Polychromatic418967fa.accept_19_16_7_8_1_8820 54 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 255 (accept_3_4 52 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 255 (accept_3_4 49 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 255 (accept_3_4 46 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 255 (accept_3_4 43 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 255 (accept_3_4 40 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 255 (accept_3_4 37 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 255 (accept_3_4 34 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 255 (accept_3_4 31 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 255
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 255 (accept_3_4 28 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 255 (accept_3_4 25 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 255 (accept_3_4 22 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 255 (accept_3_4 19 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 255 (accept_3_4 16 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 255 (accept_3_4 13 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 255 (accept_3_4 10 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 255 (accept_3_4 7 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 83 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 255 (accept_3_4 4 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  255 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 83 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 255 (accept_3_4 1 83 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 255
  (allA_succ_of_accept 81 82 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 255 (accept_3_5 80 82 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 82 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 78
  82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 255 (accept_3_5 77 82
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 76 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 82 255 (Polychromatic418967fa.accept_13_10_4_8_1_2570 75 82 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 255 (accept_3_5 74 82 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 82 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 72
  82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 255 (accept_3_5 71 82
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 255
  (Polychromatic418967fa.accept_9_7_1_3_1_443 70 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 82 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 255 (accept_3_5 68 82 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 82 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  66 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 255 (accept_3_5 65
  82 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 64 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 82 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 82 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 255 (accept_3_5 62 82 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 82 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 60
  82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 255 (accept_3_5 59 82
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 255 (Polychromatic418967fa.accept_7_2_5_3_1_98
  58 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 82 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 82 255 (accept_3_5 56 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  82 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 82 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 82 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 255 (accept_3_5 53 82 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 82 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 82 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 82 255 (accept_3_5 50 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  82 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 82 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 82 255 (accept_3_5 47 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 82 255 (Polychromatic418967fa.accept_22_2_16_13_1_10861 46 82 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 82 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 82 255 (accept_3_5 44 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  82 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 82 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 82 255 (accept_3_5 41 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 82 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 82 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 82 255
  (Polychromatic418967fa.accept_21_18_19_3_1_9649 39 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 82 255 (accept_3_5 38 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  82 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 82 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 82 255 (accept_3_5 35 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 82 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 82 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 82 255 (accept_3_5 32 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  82 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 82 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 82 255 (accept_3_5 29 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 82 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 82 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 82 255
  (Polychromatic418967fa.accept_10_7_2_5_1_298 27 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 82 255 (accept_3_5 26 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  82 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 82 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 82 255 (accept_3_5 23 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 82 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 82 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 82 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 82 255 (accept_3_5 20 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  82 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 82 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 82 255 (accept_3_5 17 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 82 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 82 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 82 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 82 255 (accept_3_5 14 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  82 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 82 255 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 82 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 82 255 (accept_3_5 11 82 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 82 255 (Polychromatic418967fa.accept_13_10_4_8_1_2570 10 82
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 82 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 82 255 (accept_3_5 8 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 82
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 82 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 82 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 82 255 (accept_3_5 5 82 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 82 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 82 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 82 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3
  82 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 255 (accept_3_5 2 82 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 255
  (allA_succ_of_accept 80 81 255 (Polychromatic418967fa.accept_18_8_9_3_1_2645 80 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 79 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 255 3 26 27 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 77 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 255 3 25 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 73 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 255 3 24 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 255 3 23 27 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 255
  (Polychromatic418967fa.accept_18_14_9_3_1_6421 68 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 255 3 22 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 65
  81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 64 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 255 3 21 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 255 (Polychromatic418967fa.accept_11_6_4_2_1_599 61 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 255 3 20 27 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 255 3 19 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024
  56 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 255 3 18 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 53 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 255 (Polychromatic418967fa.accept_19_14_5_8_1_10077 52 81
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 255 3 17 27 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 255 3 16 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 255 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 255 3 15 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 255 3 14 27 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 255 (Polychromatic418967fa.accept_16_8_1_15_1_1982 40 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 255 3 13 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 255 3 12 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 255 3 11 27 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 255
  (Polychromatic418967fa.accept_18_14_9_3_1_6421 32 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 255 3 10 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 29
  81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 255
  (Polychromatic418967fa.accept_11_6_4_2_1_599 28 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 255 3 9 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 255 3 8 27 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 255 3 7 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 19 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 255 3 6 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 255 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 255 3 5 27 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 255 3 4 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 255 3 3 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 255 3 2 27 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 81 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 255 3 1 27 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 81 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 255
  (allA_succ_of_accept 79 80 255 (accept_3_4 79 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 255 (accept_3_4 76 80 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 75 80 255 5 15 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 80 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 74 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 80 255 (accept_3_4 73 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 80 255 (Polychromatic418967fa.accept_13_7_2_8_1_1746
  72 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 80 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 255 5 14 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 68 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 80 255 (accept_3_4 67 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 80 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 66
  80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 80 255 5 13 16 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 80 255 (accept_3_4 64
  80 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 255
  (Polychromatic418967fa.accept_14_7_10_3_1_1034 63 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 80 255 (Polychromatic418967fa.accept_13_10_2_8_1_2603 62 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 80 255 (accept_3_4 61 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 80 255 5 12 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 80 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 255 (accept_3_4 58 80 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 255 (Polychromatic418967fa.accept_21_15_17_3_1_3373 57 80
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 80 255 5 11 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 80 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 80 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 255 (accept_3_4 52 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 51
  80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 255 5 10 16 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 255 (accept_3_4 49
  80 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 80 255
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 80 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 255 (accept_3_4 46 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 80 255 5 9 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 80 255 (Polychromatic418967fa.accept_21_2_17_3_1_9644 44 80 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 80 255 (accept_3_4 43 80 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 80 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 80 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 80 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 255 5 8 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 255 (Polychromatic418967fa.accept_21_18_17_3_1_4906 39 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 80 255 (accept_3_4 37 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 80 255 (Polychromatic418967fa.accept_13_10_2_8_1_2603
  36 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 80 255 5 7 16 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 80 255 (accept_3_4 34
  80 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 255
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 80 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 80 255 (accept_3_4 31 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 80 255 5 6 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 80 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 255 (accept_3_4 28 80 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 255 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 80 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 255
  (Polychromatic418967fa.accept_22_4_14_13_1_5977 26 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 80 255 5 5 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 80 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 255 (accept_3_4 22 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 255 (Polychromatic418967fa.accept_14_7_10_3_1_1034
  21 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 255 5 4 16 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 255 (accept_3_4 19
  80 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 80 255
  (Polychromatic418967fa.accept_12_6_8_3_1_82 18 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 80 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 255 (accept_3_4 16 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 80 255 5 3 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 80 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 80 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 80 255 (accept_3_4 13 80 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 80 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 80 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 80 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 80 255 5 2 16 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 80 255 (Polychromatic418967fa.accept_18_9_8_3_1_2702 9 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 255 (Polychromatic418967fa.accept_21_8_17_3_1_8031 8 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 80 255 (accept_3_4 7 80 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6
  80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 80 255 5 1 16 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 80 255 (accept_3_4 4 80
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 80 255
  (Polychromatic418967fa.accept_19_3_4_8_1_8808 3 80 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 80 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 255 (accept_3_4 1 80 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 255 (allA_succ_of_accept 78 79 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 255 (accept_3_5 77 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 79 255 (accept_3_5 74 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  79 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 79 255 (Polychromatic418967fa.accept_13_7_1_8_1_1778 72 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 255 (accept_3_5 71 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 79 255 (accept_3_5 68 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  79 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 79 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 66 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 255 (accept_3_5 65 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 255
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 255 (accept_3_5 62 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 255 (accept_3_5 59 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 255 (accept_3_5 56 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 255 (accept_3_5 53 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 255 (accept_3_5 50 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 255 (accept_3_5 47 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 255 (accept_3_5 44 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 255 (accept_3_5 41 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 255
  (Polychromatic418967fa.accept_21_18_16_3_1_8068 39 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 255 (accept_3_5 38 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 255 (accept_3_5 35 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 255 (accept_3_5 32 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 255 (Polychromatic418967fa.accept_18_12_7_3_1_2666 30 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 255 (accept_3_5 29 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 255 (accept_3_5 26 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 255 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 255 (accept_3_5 23 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 255 (accept_3_5 20 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 255 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 255 (accept_3_5 17 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 255 (accept_3_5 14 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 255 (accept_3_5 11 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 255
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 255 (accept_3_5 8 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  255 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 255 (accept_3_5 5 79 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 255
  (Polychromatic418967fa.accept_27_3_25_12_1_15556 3 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 255 (accept_3_5 2 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  255 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 255
  (allA_succ_of_accept 77 78 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 255 3 25 26 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 255 3 24 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 71
  78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 70 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 255 3 23 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 255 3 22 26 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 255 3 21 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 255 3 20 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 255 3 19 26 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 255 3 18 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 255 3 17 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 255 3 16 26 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 255 3 15 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 255 3 14 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 255 3 13 26 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 255 3 12 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 255 3 11 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 255 3 10 26 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 255 3 9 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 255 3 8 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 255 3 7 26 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 255 3 6 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 255 3 5 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 255 3 4 26 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 255 3 3 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 255 3 2 26 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 78 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 255 3 1 26 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 78 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 255
  (allA_succ_of_accept 76 77 255 (accept_3_4 76 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 255 (Polychromatic418967fa.accept_13_10_12_8_1_2550 75 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 255 (accept_3_4 73 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 77 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 71 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 255 (accept_3_4 70 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 255 (accept_3_4 67 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 65 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 255 (accept_3_4 64 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 255 (accept_3_4 61 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 77 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 255
  (Polychromatic418967fa.accept_13_7_12_8_1_199 59 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 255 (accept_3_4 58 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 255 (accept_3_4 55 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 255 (accept_3_4 52 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 255 (accept_3_4 49 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 77 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 255 (accept_3_4 46 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 255 (accept_3_4 43 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 255
  (Polychromatic418967fa.accept_22_19_11_13_1_10981 41 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 77 255 (accept_3_4 40 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 77 255 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 77 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 255 (accept_3_4 37 77 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 255
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 77 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 77 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 77 255 (accept_3_4 34 77 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 77 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32
  77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 255 (accept_3_4 31 77
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27
  30 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 255 (accept_3_4 28 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 255 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 255 (accept_3_4 25 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 77 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 255
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 255 (accept_3_4 22 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 255 (accept_3_4 19 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 255 (accept_3_4 16 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 255 (accept_3_4 13 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 77 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 255 (accept_3_4 10 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 255 (accept_3_4 7 77 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 255
  (Polychromatic418967fa.accept_13_5_12_8_1_198 5 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 255 (accept_3_4 4 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 77 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 255 (accept_3_4 1 77 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 255 (allA_succ_of_accept 75 76 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 255 (accept_3_5 74 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 255 (accept_3_5 71 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 255 (accept_3_5 68 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 255
  (Polychromatic418967fa.accept_12_6_4_3_1_361 66 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 255 (accept_3_5 65 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 255 (Polychromatic418967fa.accept_22_19_10_13_1_7775 63 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 255 (accept_3_5 62 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 255 (accept_3_5 59 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 255 (Polychromatic418967fa.accept_27_3_22_12_1_15555 57 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 255 (accept_3_5 56 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 255 (accept_3_5 53 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 255 (accept_3_5 50 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 255
  (Polychromatic418967fa.accept_13_9_11_8_1_195 48 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 255 (accept_3_5 47 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 255 (accept_3_5 44 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 255 (accept_3_5 41 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 40 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 255 (accept_3_5 38 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 255
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 255 (accept_3_5 35 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 255 (accept_3_5 32 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 255 (accept_3_5 29 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 255 (accept_3_5 26 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 255 (accept_3_5 23 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 22 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 255 (accept_3_5 20 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 255 (accept_3_5 17 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 255 (accept_3_5 14 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 255
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 255 (accept_3_5 11 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 255 (accept_3_5 8 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 255 (accept_3_5 5 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 76 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 76 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 255 (accept_3_5 2 76 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 255 (allA_succ_of_accept
  74 75 255 (Polychromatic418967fa.accept_16_10_11_15_1_6302 74 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 73 75 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 255 3 24 25 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 75 255 5 14 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 75 255 3 23 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 75 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 255 (Polychromatic418967fa.accept_13_2_10_8_1_1126 67 75
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 75 255 3 22 25 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 75 255 5 13 15 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 64 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 75 255 3 21 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 75 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 62 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 255 (Polychromatic418967fa.accept_19_4_18_8_1_10117 61 75
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 255 15 4 5 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 255
  (Polychromatic418967fa.accept_11_4_9_2_1_259 59 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 75 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 75 255 3 19 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 75 255 (Polychromatic418967fa.accept_13_4_10_8_1_1817
  56 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 255 5 11 15 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 75 255 3 18 25 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 255
  (Polychromatic418967fa.accept_21_11_12_3_1_6461 53 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 255 3 17 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 75 255 5 10 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 255 (Polychromatic418967fa.accept_16_1_11_15_1_498
  49 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 255 3 16 25 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 255
  (Polychromatic418967fa.accept_19_9_18_8_1_8782 47 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 255 (Polychromatic418967fa.accept_13_7_10_8_1_567 46 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 255 15 3 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 75 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 75 255 3 14 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 75 255 (Polychromatic418967fa.accept_13_2_10_8_1_1126 41 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 255 5 8 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 75 255 3 13 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 255 (Polychromatic418967fa.accept_13_12_10_8_1_3343 38 75
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 255 3 12 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 75 255 5 7 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 75 255 (Polychromatic418967fa.accept_21_13_12_3_1_8028 34 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 255 3 11 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 255 (Polychromatic418967fa.accept_19_13_18_8_1_4493
  32 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 255
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 31 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 255 15 2 5 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 75 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 255 3 9 25 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 255
  (Polychromatic418967fa.accept_11_4_9_2_1_259 26 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 75 255 5 5 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 75 255 3 8 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 75 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 75 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 255 3 7 25 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 75 255 5 4 15 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 255
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 19 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 255 3 6 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 255 (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 75 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 255 15 1 5 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 255
  (Polychromatic418967fa.accept_21_14_12_3_1_9637 14 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 255 (Polychromatic418967fa.accept_19_13_18_8_1_4493 13 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 255 3 4 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 255 (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 75
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 255 5 2 15 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 75 255 3 3 25 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 255 3 2 25 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 75 255 5 1 15 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 75 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 255 3 1 25 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 75 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 75 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 75
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 255 (allA_succ_of_accept
  73 74 255 (accept_3_4 73 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 255
  (Polychromatic418967fa.accept_13_7_9_8_1_188 72 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 74 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 255 (accept_3_4 70 74 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 68
  74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 255 (accept_3_4 67 74
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 255
  (Polychromatic418967fa.accept_10_6_4_5_1_615 66 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 255 (accept_3_4 64 74 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 255 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 74 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 255 (accept_3_4 61 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 255 (accept_3_4 58 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 255
  (Polychromatic418967fa.accept_10_6_4_5_1_615 56 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 255 (accept_3_4 55 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 255 (accept_3_4 52 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 74 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 255 (accept_3_4 49 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 255 (accept_3_4 46 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 255 (accept_3_4 43 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 255 (accept_3_4 40 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 74 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 255
  (Polychromatic418967fa.accept_11_5_8_2_1_588 38 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 255 (accept_3_4 37 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 255 (accept_3_4 34 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 255 (accept_3_4 31 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 255 (accept_3_4 28 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 74 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 255 (accept_3_4 25 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 255 (accept_3_4 22 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 255 (accept_3_4 19 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 255 (accept_3_4 16 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 74 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 255 (accept_3_4 13 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 255 (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 255 (accept_3_4 10 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 255 (accept_3_4 7 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 255 (accept_3_4 4 74 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 255 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 74 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 255 (Polychromatic418967fa.accept_22_2_8_13_1_10977
  2 74 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 255 (accept_3_4 1 74
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 255 (allA_succ_of_accept
  72 73 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 255 (accept_3_5 71 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 73 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 255 (accept_3_5 68 73 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 67
  73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 255 (accept_3_5 65 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 255 (Polychromatic418967fa.accept_18_9_1_3_1_6451 63 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 255 (accept_3_5 62 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 60 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 255 (accept_3_5 59 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 255 (accept_3_5 56 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 255 (Polychromatic418967fa.accept_19_17_16_8_1_2099 55 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 255 (accept_3_5 53 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 255 (accept_3_5 50 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 255
  (Polychromatic418967fa.accept_10_8_3_5_1_613 48 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 255 (accept_3_5 47 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 255 (accept_3_5 44 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 255 (accept_3_5 41 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 255 (Polychromatic418967fa.accept_19_1_16_8_1_10075 39 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 255 (accept_3_5 38 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 73 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 255
  (Polychromatic418967fa.accept_19_17_16_8_1_2099 36 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 255 (accept_3_5 35 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 255 (accept_3_5 32 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 255 (accept_3_5 29 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 255 (accept_3_5 26 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 255 (accept_3_5 23 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 255 (accept_3_5 20 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 255 (Polychromatic418967fa.accept_22_19_7_13_1_6004 19 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 255 (accept_3_5 17 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 255 (accept_3_5 14 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 255
  (Polychromatic418967fa.accept_10_2_3_5_1_996 12 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 255 (accept_3_5 11 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 255 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 255 (accept_3_5 8 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 73 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 255 (accept_3_5 5 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 255 (Polychromatic418967fa.accept_25_3_23_5_1_15554 3 73 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 255 (accept_3_5 2 73 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 255 (Polychromatic418967fa.accept_19_1_16_8_1_10075 1 73 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 255 (allA_succ_of_accept 71
  72 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 255 (Polychromatic418967fa.accept_11_4_6_2_1_51 70 72 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 255 3 23 24 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 67 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 255 3 22 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 255 (Polychromatic418967fa.accept_16_1_8_15_1_1945
  65 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 64 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 255 3 21 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 72 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 255 3 20 24 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 255
  (Polychromatic418967fa.accept_11_4_6_2_1_51 59 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 255 3 19 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 255 (Polychromatic418967fa.accept_21_14_9_3_1_4893
  56 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 255 3 18 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 255 (Polychromatic418967fa.accept_16_4_8_15_1_1113 52 72
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 255 3 17 24 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 255 (Polychromatic418967fa.accept_13_10_7_8_1_1794 49 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 255 3 16 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 255
  (Polychromatic418967fa.accept_20_6_12_15_1_3938 46 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 255 3 15 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 255 (Polychromatic418967fa.accept_16_12_8_15_1_5119 44 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 255 3 14 24 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 255 3 13 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 38
  72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 255
  (Polychromatic418967fa.accept_10_7_2_5_1_298 37 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 255 3 12 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 255 (Polychromatic418967fa.accept_13_9_7_8_1_1122 35 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 72 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 255 3 11 24 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 255
  (Polychromatic418967fa.accept_26_6_20_21_1_9972 32 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 255 (Polychromatic418967fa.accept_19_12_15_8_1_10070 31 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 255 3 10 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 255 3 9 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 255 (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 72
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 255 3 8 24 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 255
  (Polychromatic418967fa.accept_10_3_2_5_1_295 23 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 255 3 7 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 72 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 255 3 6 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 255 (Polychromatic418967fa.accept_13_3_7_8_1_4192 16 72 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 255 3 5 24 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 255
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 14 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 255 3 4 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 255 (Polychromatic418967fa.accept_22_11_6_13_1_15553 11 72
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 255
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 10 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 255 3 3 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 72 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 255 3 2 24 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 255 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 72 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 255 3 1 24 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 255 (Polychromatic418967fa.accept_13_2_7_8_1_4221 2 72 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 255
  (allA_succ_of_accept 70 71 255 (accept_3_4 70 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 255 (accept_3_4 67 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 66 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 255 (accept_3_4 64 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 255 (accept_3_4 61 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 59 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 255 (accept_3_4 58 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 255 (accept_3_4 55 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 255 (accept_3_4 52 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 255 (accept_3_4 49 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 255 (Polychromatic418967fa.accept_21_6_8_3_1_11140 48 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 255 (accept_3_4 46 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 255 (accept_3_4 43 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 255 (accept_3_4 40 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 255 (accept_3_4 37 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 255
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 35 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 255 (accept_3_4 34 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 255 (accept_3_4 31 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 255 (accept_3_4 28 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 255 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 255 (accept_3_4 25 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 255 (accept_3_4 22 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 255 (accept_3_4 19 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 255
  (Polychromatic418967fa.accept_21_17_8_3_1_9576 17 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 255 (accept_3_4 16 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 255 (accept_3_4 13 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 255 (accept_3_4 10 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 255 (accept_3_4 7 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 71 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 255 (accept_3_4 4 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  255 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 71 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 255 (accept_3_4 1 71 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 255 (allA_succ_of_accept 69 70 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 255 (accept_3_5 68 70 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 70 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 70 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 255
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 70 255 5 13 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 70 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 255 (Polychromatic418967fa.accept_19_6_13_8_1_4508 63 70
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 255 (accept_3_5 62 70 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 70 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 255 5 12 14 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 255 (accept_3_5 59
  70 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 255
  (Polychromatic418967fa.accept_9_4_7_3_1_43 58 70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 70 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 70 255 (accept_3_5 56 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 70 255 5 11 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 70 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 70 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 255 (accept_3_5 53 70 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 255 (Polychromatic418967fa.accept_19_14_13_8_1_5943 52 70
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 255 5 10 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 255 (Polychromatic418967fa.accept_20_8_10_15_1_6922 48 70
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 255 (accept_3_5 47 70 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 46
  70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 70 255 5 9 14 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 70 255 (accept_3_5 44
  70 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 70 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 255 (accept_3_5 41 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 70 255 5 8 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 70 255 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 70 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 255 (accept_3_5 38 70 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 255
  (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 70 255 5 7 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 70 255 (Polychromatic418967fa.accept_20_14_10_15_1_3952 34 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 255 (accept_3_5 32 70 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 255 5 6 14 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 255 (accept_3_5 29
  70 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 255
  (Polychromatic418967fa.accept_9_1_7_3_1_41 28 70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 70 255 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 255 (accept_3_5 26 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 70 255 5 5 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 70 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 70 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 255 (accept_3_5 23 70 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 70 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 70 255 5 4 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 70 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 70
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 255 (accept_3_5 17 70 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 255 (Polychromatic418967fa.accept_13_3_5_8_1_1099
  16 70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 70 255 5 3 14 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 70 255 (accept_3_5 14
  70 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 70 255 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 255 (accept_3_5 11 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 70 255 5 2 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 70 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 255 (accept_3_5 8 70 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 70 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 70 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 70 255 5 1 14 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 70 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 70 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 255 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 70 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 255 (accept_3_5 2 70 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 255 (allA_succ_of_accept 68 69
  255 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 255 3 22 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 65
  69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 69 255 3 21 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 69 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 69 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 69 255 3 20 23 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 69 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 255 3 19 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 55 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 69 255 3 18 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 69 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 69 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 255 3 17 23 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 255 3 16 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 47
  69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 69 255 3 15 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 69 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 69 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 255 3 14 23 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 255 3 13 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 69 255 3 12 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 69 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 255 3 11 23 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 255 3 10 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 69 255 3 9 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 69 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 255 3 8 23 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 255 3 7 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 69 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 255 3 6 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 69 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 255 3 5 23 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 255 3 4 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 69 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 255 3 3 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 69 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 255 3 2 23 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 69 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 255 3 1 23 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 69 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 255
  (allA_succ_of_accept 67 68 255 (accept_3_4 67 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  68 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 255 (accept_3_4 64 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 68 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 62 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 255 (accept_3_4 61 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 255 (accept_3_4 58 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 68 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 255 (accept_3_4 55 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 255 (accept_3_4 52 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 51 68 255 17 3 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 68 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 68 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 68 255 (accept_3_4 49 68 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 68 255 (Polychromatic418967fa.accept_13_9_3_8_1_573 48 68 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 68 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 68 255 (accept_3_4 46 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  68 255 (Polychromatic418967fa.accept_18_9_14_3_1_6407 45 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 68 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 68 255 (accept_3_4 43 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 68 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 68 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 68 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 68 255 (accept_3_4 40 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  68 255 (Polychromatic418967fa.accept_19_1_11_8_1_4504 39 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 68 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 68 255 (accept_3_4 37 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 68 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 68 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 68 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 68 255 17 2 4 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 68 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 68 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 32 68 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 68 255 (accept_3_4 31 68 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 68 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 30
  68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 68 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 68 255 (accept_3_4 28 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  68 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 68 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 68 255 (accept_3_4 25 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 68 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 68 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 68 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 68 255 (accept_3_4 22 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  68 255 (Polychromatic418967fa.accept_16_5_4_15_1_1102 21 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 68 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 68 255 (accept_3_4 19 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 68 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 68 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 68 255 17 1 4 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 68 255 (accept_3_4 16 68 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 68 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 255
  (Polychromatic418967fa.accept_16_14_4_15_1_3944 14 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 255 (accept_3_4 13 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 255 (accept_3_4 10 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 68 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 255 (accept_3_4 7 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 68 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 255 (accept_3_4 4 68 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 68 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 68
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 255 (accept_3_4 1 68 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 255 (allA_succ_of_accept 66 67
  255 (Polychromatic418967fa.accept_16_2_3_15_1_6309 66 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 67 255 (accept_3_5 65 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 67 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 67 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 255 (accept_3_5 62 67 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 61
  67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 255 (accept_3_5 59 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 255 (accept_3_5 56 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 255
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 255 (accept_3_5 53 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 255 (accept_3_5 50 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 255 (Polychromatic418967fa.accept_13_10_2_8_1_2603 49 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 255 (accept_3_5 47 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 255 (accept_3_5 44 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 255 (accept_3_5 41 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 255 (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 255 (accept_3_5 38 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 67 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 255 (accept_3_5 35 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 255 (accept_3_5 32 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 255 (Polychromatic418967fa.accept_19_12_10_8_1_3270 31 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 255
  (Polychromatic418967fa.accept_18_12_13_3_1_6427 30 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 255 (accept_3_5 29 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 255 (accept_3_5 26 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 255 (accept_3_5 23 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 255 (accept_3_5 20 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 67 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 255
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 255 (accept_3_5 17 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 255 (accept_3_5 14 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 255 (accept_3_5 11 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 255 (accept_3_5 8 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 67 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 255 (accept_3_5 5 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 67 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 255 (accept_3_5 2 67 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 255 (allA_succ_of_accept 65 66
  255 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 64 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 255 3 21 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 62
  66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 255 3 20 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 66 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 255 3 19 22 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 255 (Polychromatic418967fa.accept_14_13_10_3_1_1037 55 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 255 3 18 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 255 3 17 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 255 3 16 22 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 255
  (Polychromatic418967fa.accept_24_23_18_15_1_15552 47 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 66 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 66 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 255 3 15 22 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 66 255 (Polychromatic418967fa.accept_18_7_12_3_1_804 43 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 255 3 14 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 66 255 3 13 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 66 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 255 3 12 22 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 255
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 255 3 11 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 32
  66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 255
  (Polychromatic418967fa.accept_10_1_6_5_1_304 31 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 255 3 10 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 66 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 255 3 9 22 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 66 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 255 3 8 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 255 (Polychromatic418967fa.accept_19_4_9_8_1_8794 23 66 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 255
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 66 255 3 7 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 66 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 66 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 255 3 6 22 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 66 255 3 5 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 66 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 14 66 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 255 3 4 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 66 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 255 3 3 22 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 66 255 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 255 3 2 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 4 66 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 66 255 3 1 22 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 66 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 66 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 255 (allA_succ_of_accept 64 65 255
  (accept_3_4 64 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 255
  (Polychromatic418967fa.accept_20_3_5_15_1_2644 63 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 255 (accept_3_4 61 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 65 255 5 12 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 65 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 65 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 255 (accept_3_4 58 65 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 65 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 65 255 5 11 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 65 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 255 (accept_3_4 52 65 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 51
  65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 255 5 10 13 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 255 (accept_3_4 49
  65 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 255 (accept_3_4 46 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 255 5 9 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 255 (accept_3_4 43 65 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 255 5 8 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 255 (Polychromatic418967fa.accept_20_19_5_15_1_5380 39 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 255 (accept_3_4 37 65 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36
  65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 255 5 7 13 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 255 (accept_3_4 34
  65 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 255 (accept_3_4 31 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 65 255 5 6 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 65 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 255 (accept_3_4 28 65 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 65 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 255 5 5 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 65 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 255 (accept_3_4 22 65 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 255 (Polychromatic418967fa.accept_12_9_5_3_1_782
  21 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 255 5 4 13 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 255 (accept_3_4 19
  65 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 255 (accept_3_4 16 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 255 5 3 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 255 (accept_3_4 13 65 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 255
  (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 255 5 2 13 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 255 (accept_3_4 7 65 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 255 5 1 13 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 255 (accept_3_4 4 65
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 255
  (Polychromatic418967fa.accept_20_3_5_15_1_2644 3 65 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 255 (accept_3_4 1 65 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 255
  (allA_succ_of_accept 63 64 255 (Polychromatic418967fa.accept_19_6_7_8_1_10108 63 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 255 (accept_3_5 62 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 60
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 255 (accept_3_5 59 64
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 58 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 64 255 (Polychromatic418967fa.accept_13_5_12_8_1_198 57 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 255 (accept_3_5 56 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 64 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 54
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 255 (accept_3_5 53 64
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 255
  (Polychromatic418967fa.accept_9_7_1_3_1_443 52 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 64 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 255 (accept_3_5 50 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 64 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 255 (Polychromatic418967fa.accept_11_4_9_2_1_259
  48 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 255 (accept_3_5 47
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 46 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 64 255 (Polychromatic418967fa.accept_20_5_4_15_1_3931 45 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 255 (accept_3_5 44 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 64 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 42
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 255 (accept_3_5 41 64
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 40 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 64 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 255 (accept_3_5 38 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 64 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 255 (Polychromatic418967fa.accept_10_6_4_5_1_615
  36 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 255 (accept_3_5 35
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 255
  (Polychromatic418967fa.accept_9_7_1_3_1_443 34 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 64 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 255 (accept_3_5 32 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 64 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 30
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 255 (accept_3_5 29 64
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 255
  (Polychromatic418967fa.accept_19_9_7_8_1_3214 28 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 64 255 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 255 (accept_3_5 26 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 64 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 255 (accept_3_5 23 64
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 22 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 64 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 255 (accept_3_5 20 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 64 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 255 (accept_3_5 17 64
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 64 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 255 (accept_3_5 14 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 64 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 255 (accept_3_5 11 64
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 255
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 10 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 64 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 255 (accept_3_5 8 64 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 64 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 255 (accept_3_5 5 64 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4
  64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 255
  (Polychromatic418967fa.accept_25_3_14_5_1_13727 3 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 255 (accept_3_5 2 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 255
  (allA_succ_of_accept 62 63 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 62 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 61 63 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 255 3 20 21 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 255
  (Polychromatic418967fa.accept_19_2_6_8_1_3284 59 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 63 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 58 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 255 3 19 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 63 255 (Polychromatic418967fa.accept_13_4_11_8_1_1768
  56 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 255
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 55 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 63 255 3 18 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 63 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 53 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 63 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 255 3 17 21 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 255
  (Polychromatic418967fa.accept_18_14_9_3_1_6421 50 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 255 3 16 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 47
  63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 255
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 46 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 63 255 3 15 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 255 (Polychromatic418967fa.accept_18_8_9_3_1_2645 44 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 255 (Polychromatic418967fa.accept_13_4_11_8_1_1768 43 63
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 255 3 14 21 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 255
  (Polychromatic418967fa.accept_19_3_6_8_1_8819 41 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 40 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 255 3 13 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 38
  63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 37 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 255 3 12 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 63 255 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 255 (Polychromatic418967fa.accept_28_6_7_3_1_15551 34 63
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 255 3 11 21 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 255
  (Polychromatic418967fa.accept_10_2_3_5_1_996 32 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 255 (Polychromatic418967fa.accept_18_13_9_3_1_5114 31 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 255 3 10 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 255 (Polychromatic418967fa.accept_13_3_11_8_1_1094
  29 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 255
  (Polychromatic418967fa.accept_10_8_3_5_1_613 28 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 63 255 3 9 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 255 (Polychromatic418967fa.accept_18_8_9_3_1_2645 26 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 255 (Polychromatic418967fa.accept_14_11_7_3_1_3416 25 63
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 255 3 8 21 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 255
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 22 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 255 3 7 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 255 (Polychromatic418967fa.accept_18_2_9_3_1_3825 20 63 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 255
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 19 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 255 3 6 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 63 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 255 3 5 21 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 255
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 255 (Polychromatic418967fa.accept_18_13_9_3_1_5114 13 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 255 3 4 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 255 (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 63 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 255
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 10 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 255 3 3 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 63 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 255 3 2 21 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 255
  (Polychromatic418967fa.accept_11_5_8_2_1_588 5 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 255 (Polychromatic418967fa.accept_13_4_11_8_1_1768 4 63 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 255 3 1 21 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 63 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 255
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 1 63 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 255 (allA_succ_of_accept
  61 62 255 (accept_3_4 61 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 255 (accept_3_4 58 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 56
  62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 255 (accept_3_4 55 62
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 255
  (Polychromatic418967fa.accept_12_6_2_3_1_354 54 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 255 (accept_3_4 52 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 50
  62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 255 (accept_3_4 49 62
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 48 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 255 (accept_3_4 46 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 44
  62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 255 (accept_3_4 43 62
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 255
  (Polychromatic418967fa.accept_9_6_8_3_1_183 42 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 255 (accept_3_4 40 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 38
  62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 255 (accept_3_4 37 62
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 255
  (Polychromatic418967fa.accept_16_4_14_15_1_6331 36 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 255 (accept_3_4 34 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 32
  62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 255 (accept_3_4 31 62
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 62 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 255 (accept_3_4 28 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 62 255 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 255
  (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 62 255 (accept_3_4 25 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 62 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 255 (accept_3_4 22 62 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 255 (accept_3_4 19 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 255 (accept_3_4 16 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 62 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 255 (accept_3_4 13 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 255 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 255 (accept_3_4 10 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 255
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 255 (accept_3_4 7 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 255 (accept_3_4 4 62 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 62 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  62 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 255 (accept_3_4 1 62 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 255 (allA_succ_of_accept 60 61 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 60 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 255 (accept_3_5 59 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 255 (accept_3_5 56 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 61 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 255 (accept_3_5 53 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 255 (accept_3_5 50 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 61 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 255
  (Polychromatic418967fa.accept_11_4_6_2_1_51 48 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 255 (accept_3_5 47 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 255 (accept_3_5 44 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 61 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 255 (accept_3_5 41 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 255 (accept_3_5 38 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 255 (accept_3_5 35 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 255 (accept_3_5 32 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 61 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 255 (accept_3_5 29 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 255 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 255 (accept_3_5 26 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 255 (Polychromatic418967fa.accept_13_12_9_8_1_2595 25 61 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 255 (accept_3_5 23 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 255 (accept_3_5 20 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 61 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 255 (accept_3_5 17 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 255 (accept_3_5 14 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 61 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 255
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 255 (accept_3_5 11 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 255 (accept_3_5 8 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 255 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 61 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 255 (accept_3_5 5 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 255 (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 61 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 255 (accept_3_5 2 61 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 255 (allA_succ_of_accept 59 60 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 60 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 255 3 19 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 60 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 255 5 11 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 255 3 18 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 53
  60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 60 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 60 255 3 17 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 60 255 5 10 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 60 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 255 3 16 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 47
  60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 60 255 15 3 4 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 60 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 44 60 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 255 3 14 20 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 255 5 8 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 60 255 3 13 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 60 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 60 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 255 3 12 20 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 255 5 7 12 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 60 255 3 11 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 60 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 60 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 60 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 255 15 2 4 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 60 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 60 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 255 3 9 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 60 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60 255 5 5 12 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 255 3 8 20 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 60 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 255 3 7 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 255 5 4 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 60 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 255 3 6 20 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 60 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 255 15 1 4 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 60 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 255 3 4 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 60 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 255 5 2 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 255 3 3 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 60 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 255 3 2 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 60 255 5 1 12 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 60 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 60 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 255 3 1 20 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 60 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 255 (allA_succ_of_accept 58
  59 255 (accept_3_4 58 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 255
  (Polychromatic418967fa.accept_12_9_11_3_1_772 57 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 255 (accept_3_4 55 59 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 53
  59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 255 (accept_3_4 52 59
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 51 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 59 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 255 (accept_3_4 49 59 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 255 (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 47
  59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 255 (accept_3_4 46 59
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 255
  (Polychromatic418967fa.accept_12_9_11_3_1_772 45 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 59 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 255 (accept_3_4 43 59 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 59 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 41
  59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 255 (accept_3_4 40 59
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 255
  (Polychromatic418967fa.accept_11_6_4_2_1_599 39 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 59 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 59 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 255 (accept_3_4 37 59 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 59 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 35
  59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 255 (accept_3_4 34 59
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 255
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 59 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 255 (accept_3_4 31 59 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 59 255 (Polychromatic418967fa.accept_19_11_2_8_1_8802 30 59 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 255 (accept_3_4 28 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 255 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 255 (accept_3_4 25 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 59 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 255
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 23 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 255 (accept_3_4 22 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 255 (accept_3_4 19 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 255 (Polychromatic418967fa.accept_21_18_17_3_1_4906 18 59 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 255 (accept_3_4 16 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 255 (accept_3_4 13 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 59 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 255 (accept_3_4 10 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 255 (accept_3_4 7 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 59 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 255
  (Polychromatic418967fa.accept_19_5_2_8_1_8803 5 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 255 (accept_3_4 4 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  255 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 59 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 255 (accept_3_4 1 59 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 255
  (allA_succ_of_accept 57 58 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 255 (accept_3_5 56 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 58 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 54
  58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 255 (accept_3_5 53 58
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 255
  (Polychromatic418967fa.accept_9_7_4_3_1_204 52 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 255 (accept_3_5 50 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 48
  58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 255 (accept_3_5 47 58
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 255
  (Polychromatic418967fa.accept_9_1_4_3_1_201 46 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 255 (accept_3_5 44 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 58 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 42
  58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 255 (accept_3_5 41 58
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 58 255 (Polychromatic418967fa.accept_21_18_16_3_1_8068 39 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 255 (accept_3_5 38 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 58 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36
  58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 255 (accept_3_5 35 58
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 58 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 255 (accept_3_5 32 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 58 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 58 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  30 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 255 (accept_3_5 29
  58 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 255
  (Polychromatic418967fa.accept_9_1_4_3_1_201 28 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 58 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 255 (accept_3_5 26 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 58 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24
  58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 255 (accept_3_5 23 58
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 58 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 255 (accept_3_5 20 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 58 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  18 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 255 (accept_3_5 17
  58 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 255
  (Polychromatic418967fa.accept_9_7_4_3_1_204 16 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 58 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 255 (accept_3_5 14 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 58 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12
  58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 255 (accept_3_5 11 58
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 255
  (Polychromatic418967fa.accept_9_1_4_3_1_201 10 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 58 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 255 (accept_3_5 8 58 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 58 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 255 (accept_3_5 5 58 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58 255 (Polychromatic418967fa.accept_22_4_14_13_1_5977
  4 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 255
  (Polychromatic418967fa.accept_10_3_8_5_1_606 3 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 58 255 (accept_3_5 2 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58
  255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 255 (allA_succ_of_accept 56
  57 255 (Polychromatic418967fa.accept_16_8_9_15_1_5112 56 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 57 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 55 57 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 255 3 18 19 85 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 57 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 52 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 255 3 17 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 57 255 3 16 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 57 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 255 3 15 19 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 255 3 14 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 41
  57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 40 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 57 255 3 13 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 57 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 57 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 255 3 12 19 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 255 3 11 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 32
  57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 57 255 3 10 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 57 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 57 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 255 3 9 19 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 255 3 8 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 57 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 57 255 3 7 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 57 255 (Polychromatic418967fa.accept_25_20_7_5_1_13759 20 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 57 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 255 3 6 19 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 255 3 5 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 255
  (Polychromatic418967fa.accept_10_3_7_5_1_288 13 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 57 255 3 4 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 57 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 255 3 3 19 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 255
  (Polychromatic418967fa.accept_10_8_7_5_1_602 8 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 255 3 2 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 57 255 3 1 19 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 57 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 57 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 255 (allA_succ_of_accept 55 56 255
  (accept_3_4 55 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 56 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 56 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 255 (accept_3_4 52 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 56 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 56 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 50
  56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 56 255 (accept_3_4 49 56
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 56 255
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 48 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 56 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 255 (accept_3_4 46 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 56 255 (Polychromatic418967fa.accept_18_9_2_3_1_5082 45 56 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 44
  56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 56 255 (accept_3_4 43 56
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 56 255
  (Polychromatic418967fa.accept_9_6_2_3_1_771 42 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 56 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 255 (accept_3_4 40 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 56 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 56 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 255 (Polychromatic418967fa.accept_13_12_4_8_1_1120
  38 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 255 (accept_3_4 37
  56 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 255
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 56 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 255 (accept_3_4 34 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 56 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 56 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 32
  56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 56 255 (accept_3_4 31 56
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 56 255
  (Polychromatic418967fa.accept_12_6_8_3_1_82 30 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 56 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 255 (accept_3_4 28 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 56 255 (Polychromatic418967fa.accept_18_9_2_3_1_5082 27 56 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 26
  56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 56 255 (accept_3_4 25 56
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 56 255
  (Polychromatic418967fa.accept_9_6_2_3_1_771 24 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 56 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 255 (accept_3_4 22 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 56 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 56 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 255 (Polychromatic418967fa.accept_16_4_8_15_1_1113
  20 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 255 (accept_3_4 19
  56 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 255
  (Polychromatic418967fa.accept_12_6_8_3_1_82 18 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 56 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 255 (accept_3_4 16 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 56 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 56 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 14
  56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 56 255 (accept_3_4 13 56
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 56 255
  (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 56 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 255 (accept_3_4 10 56 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 56 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 56 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 8
  56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 56 255 (accept_3_4 7 56 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6
  56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 56 255 (accept_3_4 4 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56
  255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 56 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 56 255 (Polychromatic418967fa.accept_21_2_14_3_1_4933 2 56 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 255 (accept_3_4 1 56 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 56 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 255
  (allA_succ_of_accept 54 55 255 (Polychromatic418967fa.accept_16_6_7_15_1_1942 54 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 255 (accept_3_5 53 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 55 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 51
  55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 255 5 10 11 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 255 (Polychromatic418967fa.accept_13_9_3_8_1_573 48 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 255 (accept_3_5 47 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 55 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 255 5 9 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 255 (accept_3_5 44 55 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 55 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 255 (accept_3_5 41 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  255 5 8 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 255 (accept_3_5 38 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 255 (Polychromatic418967fa.accept_22_14_11_13_1_13934 36 55
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 255 5 7 11 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 34 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 255 (accept_3_5 32 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 55 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 255 5 6 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 255 (accept_3_5 29 55 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 255
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 255 (accept_3_5 26 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  255 5 5 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 255 (accept_3_5 23 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 55 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 255 5 4 11 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 255
  (Polychromatic418967fa.accept_16_3_7_15_1_1130 19 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 255 (accept_3_5 17 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 255 5 3 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 255 (accept_3_5 14 55 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 55 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 255
  (Polychromatic418967fa.accept_18_12_1_3_1_7843 12 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 255 (accept_3_5 11 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  255 5 2 11 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 55 255 (accept_3_5 8 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 55 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 55 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 255 5 1 11 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 255 (Polychromatic418967fa.accept_16_3_7_15_1_1130 3 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 255 (accept_3_5 2 55 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 255 (Polychromatic418967fa.accept_23_1_9_2_1_15550 1 55 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 255)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 255 (allA_succ_of_accept 53 54 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 54 255 3 17 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 54 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 255 3 16 18 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 255
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 47 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 255 3 15 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 44
  54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 255 3 14 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 54 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 255 3 13 18 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 255
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 255 3 12 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 255 (Polychromatic418967fa.accept_21_14_12_3_1_9637
  35 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 255
  (Polychromatic418967fa.accept_11_1_10_2_1_58 34 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 54 255 3 11 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 54 255 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 54 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 255 3 10 18 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 255 3 9 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 255 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 54 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 255 3 8 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 54 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 255 3 7 18 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 255
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 255 3 6 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 54 255 3 5 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 54 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 255 3 4 18 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 255
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 255 3 3 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 54 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 255
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 255 3 2 18 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 54 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 255 3 1 18 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 54 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 255)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  255 (allA_succ_of_accept 52 53 255 (accept_3_4 52 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 255 (accept_3_4 49 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 53 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 47 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 255 (accept_3_4 46 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 255 (accept_3_4 43 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 255 (accept_3_4 40 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 255 (Polychromatic418967fa.accept_19_1_15_8_1_4538 39 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 255 (accept_3_4 37 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 255
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 255 (accept_3_4 34 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 255 (accept_3_4 31 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 255 (accept_3_4 28 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 255 (accept_3_4 25 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 53 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 255 (accept_3_4 22 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 255 (accept_3_4 19 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 255
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 255 (accept_3_4 16 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 255 (accept_3_4 13 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 53 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 255 (accept_3_4 10 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 255 (accept_3_4 7 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 255 (accept_3_4 4 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  255 (Polychromatic418967fa.accept_19_3_15_8_1_3232 3 53 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 53 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 255 (accept_3_4 1 53 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 53 255))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 255
  (allA_succ_of_accept 51 52 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 52 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 255 (accept_3_5 50 52 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 255 (Polychromatic418967fa.accept_10_8_2_5_1_596
  48 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 255 (accept_3_5 47
  52 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 255
  (Polychromatic418967fa.accept_9_1_7_3_1_41 46 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 52 255 (Polychromatic418967fa.accept_19_7_14_8_1_4535 45 52 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 255 (accept_3_5 44 52 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 52 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 42
  52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 52 255 (accept_3_5 41 52
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 52 255 (Polychromatic418967fa.accept_9_4_7_3_1_43
  40 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 52 255
  (Polychromatic418967fa.accept_21_18_10_3_1_9672 39 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 52 255 (accept_3_5 38 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  52 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 52 255 (Polychromatic418967fa.accept_21_15_10_3_1_9578 36 52 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 255 (accept_3_5 35 52 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 255 (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 52
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 255 (accept_3_5 32 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 52 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 255 (accept_3_5 29 52 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 52 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 52 255 (accept_3_5 26 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  52 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 52 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 52 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 255 (accept_3_5 23 52 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 52 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 255
  (Polychromatic418967fa.accept_14_7_10_3_1_1034 21 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 255 (accept_3_5 20 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 52 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 255 (accept_3_5 17 52 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 52 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 255 (accept_3_5 14 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  52 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 52 255 (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 52 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 52 255 (accept_3_5 11 52 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 52 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 52 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 255
  (Polychromatic418967fa.accept_19_9_14_8_1_11549 9 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 52 255 (accept_3_5 8 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 52 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 52 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 52 255 (accept_3_5 5 52 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 52 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 52 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 52 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  52 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 255 (accept_3_5 2 52 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  255)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 255 (allA_succ_of_accept 50 51 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 255 3 16 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 255 3 15 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 51 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 255 3 14 17 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 255 3 13 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 38
  51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 255
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 255 3 12 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 51 255 17 2 3 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 51 255 3 11 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 51 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 255 3 10 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 51 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 255 3 9 17 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 255 3 8 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 51 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 255 3 7 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 51 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 255 3 6 17 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 17 51 255 17 1 3 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 51 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 51 255 3 5 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 51 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 51 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 255 3 4 17 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 255 3 3 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 51 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 255 3 2 17 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 51 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 255 3 1 17 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 51 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 51 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 255))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 255
  (allA_succ_of_accept 49 50 255 (accept_3_4 49 50 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  50 255 (Polychromatic418967fa.accept_11_4_6_2_1_51 48 50 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 50 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 50 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 255 (accept_3_4 46 50 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 45 50 255 5 9 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 50 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 50 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 255 (accept_3_4 43 50 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 50 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 50 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 255 5 8 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 50 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 50 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 255 (accept_3_4 37 50 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 255
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 50 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 50 255 5 7 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 50 255 (accept_3_4 34 50 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  50 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 50 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 50 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 255 (accept_3_4 31 50 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 255 5 6 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 50 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 255 (accept_3_4 28 50 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 50
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 50 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 50 255 5 5 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 50 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 50 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 255 (accept_3_4 22 50 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  50 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 255 5 4 10 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 255 (accept_3_4 19
  50 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 50 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 255 (accept_3_4 16 50 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 50 255 5 3 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 50 255 (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 50 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 255 (accept_3_4 13 50 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 50 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 50 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 50 255 5 2 10 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 50 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 50 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 255 (accept_3_4 7 50 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6
  50 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 50 255 5 1 10 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 50 255 (accept_3_4 4 50
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50 255
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 50 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 50 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 50 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 255 (accept_3_4 1 50 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 255)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 255 (allA_succ_of_accept
  48 49 255 (Polychromatic418967fa.accept_18_12_13_3_1_6427 48 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 49 255 (accept_3_5 47 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 49 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 49 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 255 (accept_3_5 44 49 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 43
  49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 255 (accept_3_5 41 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 255 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 49 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 255 (accept_3_5 38 49 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 49 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 255
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 255 (accept_3_5 35 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 49 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 255 (accept_3_5 32 49 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 255 (accept_3_5 29 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 255 (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 49 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 255 (accept_3_5 26 49 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 49 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 255 (accept_3_5 23 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 49 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 255 (accept_3_5 20 49 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 49 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 255 (accept_3_5 17 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 49 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 255 (accept_3_5 14 49 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 255 (Polychromatic418967fa.accept_23_13_3_2_1_15549 13 49 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 255
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 255 (accept_3_5 11 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 255 (accept_3_5 8 49 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 49 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 255 (accept_3_5 5 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 255 (Polychromatic418967fa.accept_19_3_11_8_1_3193 3 49 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 255 (accept_3_5 2 49 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 49 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 255))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 255 (allA_succ_of_accept 47 48 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 48 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 46
  48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 255 3 15 16 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 43 48 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 255 3 14 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 255 (Polychromatic418967fa.accept_21_20_6_3_1_9691
  41 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 255
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 40 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 48 255 3 13 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 48 255 (Polychromatic418967fa.accept_13_12_9_8_1_2595 38 48 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 255 3 12 16 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 255
  (Polychromatic418967fa.accept_19_16_10_8_1_10067 35 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 48 255 (Polychromatic418967fa.accept_20_14_8_15_1_8432 34 48 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 255 3 11 16 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 48 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 48 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 255 3 10 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 255 (Polychromatic418967fa.accept_13_3_9_8_1_4202
  29 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 255
  (Polychromatic418967fa.accept_11_6_4_2_1_599 28 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 48 255 3 9 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 48 255 (Polychromatic418967fa.accept_18_8_12_3_1_2708 26 48 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 255 3 8 16 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 48 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 255 3 7 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 48 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 255
  (Polychromatic418967fa.accept_18_1_12_3_1_6426 19 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 255 3 6 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 48 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 48 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 255 3 5 16 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 255
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 14 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 48 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 255 3 4 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 255
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 48 255 3 3 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 48 255 (Polychromatic418967fa.accept_18_8_12_3_1_2708 8 48 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 48 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 255 3 2 16 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 255
  (Polychromatic418967fa.accept_19_5_10_8_1_8775 5 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 48 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 255 3 1 16 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 48 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 255
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 1 48 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 255)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 255 (allA_succ_of_accept 46 47 255
  (accept_3_4 46 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 255
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 255 (accept_3_4 43 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 47 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 41
  47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 255 (accept_3_4 40 47
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 255
  (Polychromatic418967fa.accept_19_1_9_8_1_4474 39 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 255 (accept_3_4 37 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 35
  47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 255 (accept_3_4 34 47
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 255
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 255 (accept_3_4 31 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 47 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 255 (accept_3_4 28 47
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 255
  (Polychromatic418967fa.accept_21_6_5_3_1_12588 27 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 255 (accept_3_4 25 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 47 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 255 (accept_3_4 22 47
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 255
  (Polychromatic418967fa.accept_12_9_11_3_1_772 21 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 255 (accept_3_4 19 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 47 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 17
  47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 255 (accept_3_4 16 47
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 255 (accept_3_4 13 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 47 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 255
  (Polychromatic418967fa.accept_19_11_9_8_1_11507 11 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 255 (accept_3_4 10 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 255 (accept_3_4 7 47 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 47 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 255 (accept_3_4 4 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 47 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 255 (accept_3_4 1 47 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 255))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 255 (allA_succ_of_accept 45
  46 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 46 255 (accept_3_5 44 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 46 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 46 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 46 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 255 (accept_3_5 41 46 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 40
  46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 255
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 255 (accept_3_5 38 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 46 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 255 (accept_3_5 35 46 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 46 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 255 (accept_3_5 32 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 46 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 255 (accept_3_5 29 46 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 255 (Polychromatic418967fa.accept_13_2_7_8_1_4221 28 46 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 255 (accept_3_5 26 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 46 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 255 (accept_3_5 23 46 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 46 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 255 (accept_3_5 20 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 255 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 46 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 255 (accept_3_5 17 46 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 46 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 255 (accept_3_5 14 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 255 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 46 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 255 (accept_3_5 11 46 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 255 (Polychromatic418967fa.accept_13_10_7_8_1_1794 10 46
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 255 (accept_3_5 8 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 46 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 255 (accept_3_5 5 46 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 46 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 255 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3
  46 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 255 (accept_3_5 2 46 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  255)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 255 (allA_succ_of_accept 44 45 255
  (Polychromatic418967fa.accept_16_12_13_15_1_1966 44 45 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 45 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 45 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 255 3 14 15 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 45 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 45 255 5 8 9 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 45 255 3 13 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 45 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 255 3 12 15 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 45 255 5 7 9 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 45 255 3 11 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 45 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 45 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 45 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 255 15 2 3 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 45 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 255 (Polychromatic418967fa.accept_13_2_6_8_1_1092 28 45 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 255 3 9 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 255 5 5 9 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 45 255 3 8 15 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 45 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 255 3 7 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 45 255 5 4 9 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 255 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 45 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 255 3 6 15 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 255
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 45 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 255 (Polychromatic418967fa.accept_19_16_7_8_1_8820 16 45 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 255 15 1 3 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 45 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 255 3 4 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 255 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 45 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 255 5 2 9 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 45 255 3 3 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 255 (Polychromatic418967fa.accept_18_8_9_3_1_2645 8 45 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 45 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 45 255 3 2 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 45 255 5 1 9 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 255 (Polychromatic418967fa.accept_20_4_5_15_1_6869 4 45 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 255 3 1 15 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 255
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 45 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 255))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 255 (allA_succ_of_accept 43 44 255
  (accept_3_4 43 44 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 255
  (Polychromatic418967fa.accept_9_6_8_3_1_183 42 44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 255 (accept_3_4 40 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 44 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 38
  44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 255 (accept_3_4 37 44
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 255 (accept_3_4 34 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 44 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 32
  44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 255 (accept_3_4 31 44
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 255
  (Polychromatic418967fa.accept_12_6_8_3_1_82 30 44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 44 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 255 (accept_3_4 28 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 44 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 44 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 26
  44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 255 (accept_3_4 25 44
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 255
  (Polychromatic418967fa.accept_9_6_8_3_1_183 24 44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 255 (accept_3_4 22 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 255 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 44 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 20
  44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 255 (accept_3_4 19 44
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 255
  (Polychromatic418967fa.accept_12_6_8_3_1_82 18 44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 44 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 255 (accept_3_4 16 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 44 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 44 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 14
  44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 255 (accept_3_4 13 44
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 44 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 255 (accept_3_4 10 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 44 255 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 44 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8
  44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 255 (accept_3_4 7 44 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 255 (accept_3_4 4 44 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 44 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 255 (accept_3_4 1 44 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 255)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 255 (allA_succ_of_accept 42 43
  255 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 255 (accept_3_5 41 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 255 (accept_3_5 38 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 43 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 255 (accept_3_5 35 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 255 (accept_3_5 32 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 43 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 255 (accept_3_5 29 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 255 (accept_3_5 26 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 43 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 255 (accept_3_5 23 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 255 (accept_3_5 20 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 255 (accept_3_5 17 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 255 (accept_3_5 14 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 43 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 255 (accept_3_5 11 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 255 (accept_3_5 8 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 255 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 255 (accept_3_5 5 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 255 (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 43 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 255 (accept_3_5 2 43 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 43 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 255))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 255
  (allA_succ_of_accept 41 42 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 42 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 255 3 13 14 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 42 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 255 3 12 14 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  42 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 42 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 42 255 3 11 14 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 42 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 42 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 42 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 255 3 10 14 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 42 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 255 3 9 14 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 42 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 255 3 8 14 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 42 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 42 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 255 3 7 14 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 42 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 42 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 255 3 6 14 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 42 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 255 3 5 14 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 42 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 42 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 255 3 4 14 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 42 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 42 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 255 3 3 14 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 42 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 42 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 255 3 2 14 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 42 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 255 3 1 14 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 42 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 255)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 255
  (allA_succ_of_accept 40 41 255 (accept_3_4 40 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 255 (accept_3_4 37 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 255 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 41 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 255 (accept_3_4 34 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 255 (accept_3_4 31 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 41 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 255
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 255 (accept_3_4 28 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 255 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 255 (accept_3_4 25 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 41 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 255 (accept_3_4 22 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 255 (accept_3_4 19 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 255 (accept_3_4 16 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 255 (accept_3_4 13 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 255 (Polychromatic418967fa.accept_21_12_20_3_1_12578 12 41 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 255 (accept_3_4 10 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 255 (accept_3_4 7 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 255
  (Polychromatic418967fa.accept_11_5_8_2_1_588 5 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 255 (accept_3_4 4 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  255 (Polychromatic418967fa.accept_25_3_16_5_1_15548 3 41 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 41 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 255 (accept_3_4 1 41 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 41 255))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 255 (allA_succ_of_accept
  39 40 255 (Polychromatic418967fa.accept_16_7_8_15_1_6327 39 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 40 255 (accept_3_5 38 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 40 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 40 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 40 255 5 7 8 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 40 255
  (Polychromatic418967fa.accept_9_7_4_3_1_204 34 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 40 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 40 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 40 255 (accept_3_5 32 40 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 40 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 255 5 6 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 255 (accept_3_5 29 40 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 40 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 255
  (Polychromatic418967fa.accept_21_6_19_3_1_4823 27 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 255 (accept_3_5 26 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40
  255 5 5 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  40 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 40 255 (accept_3_5 23 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 40 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 40 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 255 (Polychromatic418967fa.accept_24_21_16_15_1_15547 21 40
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 255 5 4 8 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 40 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 40 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 255 (accept_3_5 17 40 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 40 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 40 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 40 255 5 3 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 40 255 (accept_3_5 14 40 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 40 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 255
  (Polychromatic418967fa.accept_13_12_1_8_1_1779 12 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 255 (accept_3_5 11 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  255 5 2 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40
  255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 255 (accept_3_5 8 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 40 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 40 255 5 1 8 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 40 255 (Polychromatic418967fa.accept_16_4_8_15_1_1113 4 40 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 255
  (Polychromatic418967fa.accept_27_3_13_12_1_15546 3 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 255 (accept_3_5 2 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 255)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 255 (allA_succ_of_accept 38 39 255
  (Polychromatic418967fa.accept_16_6_7_15_1_1942 38 39 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 255 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 39 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 255 3 12 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 255 (Polychromatic418967fa.accept_14_7_11_3_1_5365
  35 39 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 39 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 255 3 11 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 255 (Polychromatic418967fa.accept_19_13_1_8_1_3281 32 39 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 39 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 255 3 10 13 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 39 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 255 (Polychromatic418967fa.accept_19_9_1_8_1_12907 28 39 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 255 3 9 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 255 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 39 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 255
  (Polychromatic418967fa.accept_20_5_19_15_1_3946 25 39 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 255 3 8 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 255 (Polychromatic418967fa.accept_21_2_18_3_1_9697 23 39 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 39 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 255 3 7 13 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 39 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 255 (Polychromatic418967fa.accept_16_3_7_15_1_1130 19 39 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 255 3 6 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 255 (Polychromatic418967fa.accept_20_17_19_15_1_6859 17 39
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 255
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 39 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 255 3 5 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 39 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 39 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 255 3 4 13 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 255
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 39 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 255 (Polychromatic418967fa.accept_20_10_19_15_1_2692 10 39 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 255 3 3 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 39 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 255
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 39 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 255 3 2 13 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 255 (Polychromatic418967fa.accept_20_5_19_15_1_3946 5 39 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 39 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 255 3 1 13 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 255
  (Polychromatic418967fa.accept_19_2_1_8_1_7279 2 39 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 39 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 255))))))))))))))))))))))))))))))))))))))) (allB_succ 38 255
  (allA_succ_of_accept 37 38 255 (accept_3_4 37 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 255 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 255 (accept_3_4 34 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 255 (accept_3_4 31 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 255 (accept_3_4 28 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 38 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 255 (accept_3_4 25 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 255 (accept_3_4 22 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 255
  (Polychromatic418967fa.accept_13_7_12_8_1_199 20 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 255 (accept_3_4 19 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 255 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 255 (accept_3_4 16 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 38 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 255
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 255 (accept_3_4 13 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 255 (accept_3_4 10 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 255 (accept_3_4 7 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 255 (accept_3_4 4 38 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 255 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 38 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 2
  38 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 255 (accept_3_4 1 38 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 255)))))))))))))))))))))))))))))))))))))) (allB_succ 37 255
  (allA_succ_of_accept 36 37 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 255 (accept_3_5 35 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 255 (accept_3_5 32 37
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 255
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 255 (accept_3_5 29 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 27
  37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 255 (accept_3_5 26 37
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 255
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 255 (accept_3_5 23 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 255 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 255 (accept_3_5 20
  37 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 255 (accept_3_5 17 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 255 (accept_3_5 14 37
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 255
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 255 (accept_3_5 11 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 255 (Polychromatic418967fa.accept_11_9_4_2_1_600 9
  37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 255 (accept_3_5 8 37 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7
  37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 255 (accept_3_5 5 37 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 255 (accept_3_5 2 37 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 255))))))))))))))))))))))))))))))))))))) (allB_succ 36 255
  (allA_succ_of_accept 35 36 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 36 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 255 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 36 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 255 3 11 12 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 36 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 255 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 36 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 255 3 10 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 255 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  29 36 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 255
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 28 36 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 255 3 9 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 36 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 255 3 8 12 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 255 (Polychromatic418967fa.accept_19_3_17_8_1_5916 22 36 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 255 3 7 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 255 (Polychromatic418967fa.accept_13_7_10_8_1_567 20 36 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 255 3 6 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 255 (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 36 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 36 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 255 3 5 12 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 255
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 36 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 255 (Polychromatic418967fa.accept_24_13_12_15_1_15545 13 36 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 255 3 4 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  36 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 255
  (Polychromatic418967fa.accept_19_10_17_8_1_5917 10 36 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 255 3 3 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 255 (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 36 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 255 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 36 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 255 3 2 12 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 36 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 255 3 1 12 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 36 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 255
  (Polychromatic418967fa.accept_10_1_6_5_1_304 1 36 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 255)))))))))))))))))))))))))))))))))))) (allB_succ 35 255 (allA_succ_of_accept 34 35 255 (accept_3_4 34
  35 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 255
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 35 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 255 (accept_3_4 31 35 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 35 255 5 6 7 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 35 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 35 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 255 (accept_3_4 28 35 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 255 (Polychromatic418967fa.accept_13_1_9_8_1_1734 27 35 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 35 255 5 5 7 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 35 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 35 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 35 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 255 (accept_3_4 22 35 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 255 (Polychromatic418967fa.accept_12_9_11_3_1_772
  21 35 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 35 255 5 4 7 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 35 255 (accept_3_4 19
  35 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 255
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 35 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 35 255 (Polychromatic418967fa.accept_13_4_9_8_1_1736 17 35 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 255 (accept_3_4 16 35 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 35 255 5 3 7 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 35 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 35 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 255 (accept_3_4 13 35 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 255 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 35 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 35 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 255 5 2 7 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 255 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 35 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 255 (accept_3_4 7 35 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6
  35 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 35 255 5 1 7 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 35 255 (accept_3_4 4 35
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 255
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 35 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 255 (accept_3_4 1 35 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 255))))))))))))))))))))))))))))))))))) (allB_succ 34 255 (allA_succ_of_accept 33 34 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 255 (accept_3_5 32 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 34 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 255 (accept_3_5 29 34 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 34 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 255
  (Polychromatic418967fa.accept_21_6_13_3_1_4851 27 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 255 (accept_3_5 26 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 34 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 255 (accept_3_5 23 34 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 34 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 255 (accept_3_5 20 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 34 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 34 255 17 1 2 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 34 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 16
  34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 255 (accept_3_5 14 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 255 (Polychromatic418967fa.accept_16_12_2_15_1_490 12 34 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 255 (accept_3_5 11 34 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 34 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 255 (accept_3_5 8 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 255 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 34 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 255 (accept_3_5 5 34 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 34 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3
  34 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 255 (accept_3_5 2 34 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 255))))))))))))))))))))))))))))))))))
  (allB_succ 33 255 (allA_succ_of_accept 32 33 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 33 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 33 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 255 3 10 11 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 33 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 33 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 255 3 9 11 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 33 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 255 3 8 11 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 33 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 255 3 7 11 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 33 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 33 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 255 3 6 11 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 33 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 255 3 5 11 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 33 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 255 3 4 11 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 255 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 33 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 255 3 3 11 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 255
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 33 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 33 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 255 3 2 11 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 33 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 255
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 33 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 255 3 1 11 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 33 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 255)))))))))))))))))))))))))))))))))
  (allB_succ 32 255 (allA_succ_of_accept 31 32 255 (accept_3_4 31 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 255 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 32 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 255 (accept_3_4 28 32 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 27
  32 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 255
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 255 (accept_3_4 25 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 255 (accept_3_4 22 32 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 255 (Polychromatic418967fa.accept_14_7_4_3_1_488 21 32 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 255
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 255 (accept_3_4 19 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 255 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 255 (accept_3_4 16 32 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 32 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 255
  (Polychromatic418967fa.accept_13_1_6_8_1_208 14 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 255 (accept_3_4 13 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 255 (accept_3_4 10 32 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 255 (Polychromatic418967fa.accept_18_9_14_3_1_6407 9 32 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 255 (accept_3_4 7 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 32 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 255 (accept_3_4 4 32 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 32 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 32
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 255 (accept_3_4 1 32 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 255)))))))))))))))))))))))))))))))) (allB_succ 31 255
  (allA_succ_of_accept 30 31 255 (Polychromatic418967fa.accept_18_12_13_3_1_6427 30 31 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 255 (accept_3_5 29 31 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 255 (Polychromatic418967fa.accept_13_1_5_8_1_207
  27 31 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 255 (accept_3_5 26
  31 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 255
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 31 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 31 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 255 (accept_3_5 23 31 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 255 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  21 31 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 255 (accept_3_5 20
  31 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 255
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 31 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 31 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 255 (accept_3_5 17 31 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  31 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 255 (accept_3_5 14 31
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 255
  (Polychromatic418967fa.accept_20_13_11_15_1_6881 13 31 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 255 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 31 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 255 (accept_3_5 11 31 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 31 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 255 (accept_3_5 8 31 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 31 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 31 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 255 (accept_3_5 5 31 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 255 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3
  31 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 255 (accept_3_5 2 31 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  31 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 255)))))))))))))))))))))))))))))))
  (allB_succ 30 255 (allA_succ_of_accept 29 30 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 30 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 30 255 3 9 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 30 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 30 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 255 5 5 6 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 255 3 8 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 255 (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 30 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 30 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 255 3 7 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 255 5 4 6 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 255 3 6 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 30 255
  (Polychromatic418967fa.accept_11_5_8_2_1_588 16 30 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 30 255 15 1 2 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 30 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 30 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 255 3 4 10 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 255
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 30 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 30 255 5 2 6 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 30 255 3 3 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 30 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 30 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 255 (Polychromatic418967fa.accept_16_7_14_15_1_2932 7 30 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 255 3 2 10 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 255 5 1 6 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 30 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 30 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 255 3 1 10 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 30 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 255)))))))))))))))))))))))))))))) (allB_succ
  29 255 (allA_succ_of_accept 28 29 255 (accept_3_4 28 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 255 (Polychromatic418967fa.accept_21_6_8_3_1_11140 27 29 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 255 (accept_3_4 25 29 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 24
  29 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 255 (accept_3_4 22 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 255 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 255 (accept_3_4 19 29 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 255
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 255 (accept_3_4 16 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 255 (accept_3_4 13 29 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 255 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 255
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 255 (accept_3_4 10 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 255 (accept_3_4 7 29 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 255 (accept_3_4 4 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  255 (Polychromatic418967fa.accept_16_3_13_15_1_1913 3 29 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 29 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 255 (accept_3_4 1 29 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 29 255))))))))))))))))))))))))))))) (allB_succ 28 255 (allA_succ_of_accept 27 28 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 255 (accept_3_5 26 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 28 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 255 (accept_3_5 23 28 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 28 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 255
  (Polychromatic418967fa.accept_25_21_3_5_1_15544 21 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 255 (accept_3_5 20 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 255 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 28 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 255 (accept_3_5 17 28 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 28 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 255 (accept_3_5 14 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 28 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 255 (accept_3_5 11 28 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 255 (Polychromatic418967fa.accept_13_10_2_8_1_2603 10 28 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 255
  (Polychromatic418967fa.accept_21_9_7_3_1_4888 9 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 255 (accept_3_5 8 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 255 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 28 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 255 (accept_3_5 5 28 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 28 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 255 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  28 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 255 (accept_3_5 2 28 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 255))))))))))))))))))))))))))))
  (allB_succ 27 255 (allA_succ_of_accept 26 27 255 (Polychromatic418967fa.accept_16_10_11_15_1_6302 26 27 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 27 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 255 3 8 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 27 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 22 27 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 255 3 7 9 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 27 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 255 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 27 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 255 3 6 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 255 (Polychromatic418967fa.accept_16_1_11_15_1_498 17 27 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 255 3 5 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 255 (Polychromatic418967fa.accept_18_14_9_3_1_6421 14 27 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 255 3 4 9 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 255 (Polychromatic418967fa.accept_14_10_13_3_1_2552 10 27 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 255 3 3 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 255 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 27 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 255
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 27 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 255 3 2 9 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 255 (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 27 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 255 3 1 9 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 27 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 255 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 27 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 255))))))))))))))))))))))))))) (allB_succ 26 255 (allA_succ_of_accept 25
  26 255 (accept_3_4 25 26 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 255
  (Polychromatic418967fa.accept_9_6_8_3_1_183 24 26 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 255 (accept_3_4 22 26 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 255 (Polychromatic418967fa.accept_9_2_8_3_1_181 20
  26 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 255 (accept_3_4 19 26
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 255
  (Polychromatic418967fa.accept_12_6_2_3_1_354 18 26 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 255 (accept_3_4 16 26 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 26 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 255 (Polychromatic418967fa.accept_9_5_8_3_1_437 14
  26 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 255 (accept_3_4 13 26
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 255
  (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 26 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 26 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 255 (accept_3_4 10 26 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 26 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 8
  26 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 255 (accept_3_4 7 26 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6
  26 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 255 (accept_3_4 4 26 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  255 (Polychromatic418967fa.accept_22_3_4_13_1_13947 3 26 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 26 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 26 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 255 (accept_3_4 1 26 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 26 255)))))))))))))))))))))))))) (allB_succ 25 255 (allA_succ_of_accept 24 25 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 25 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 255 (accept_3_5 23 25 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 25 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 25 255 5 4 5 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 25 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 19
  25 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 255 (accept_3_5 17 25 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 25 255 5 3 5 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 25 255 (accept_3_5 14 25 255 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 25 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 255 (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 25 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 255 (accept_3_5 11 25 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 25 255 5 2 5 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 25 255 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  25 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 255 (accept_3_5 8 25 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 255 (Polychromatic418967fa.accept_13_7_12_8_1_199 7
  25 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 255 5 1 5 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 255 (Polychromatic418967fa.accept_19_3_6_8_1_8819 3 25 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 255 (accept_3_5 2 25 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 255 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 255))))))))))))))))))))))))) (allB_succ
  24 255 (allA_succ_of_accept 23 24 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 24 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 22
  24 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 255 3 7 8 85 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 24 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 24 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 255 3 6 8 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 24 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 24 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 255 3 5 8 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 24 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 24 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 255 3 4 8 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 24 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 24 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 255 3 3 8 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 255 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 24 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 255
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 24 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 255 3 2 8 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 255 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 24 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 24 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 255 3 1 8 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 255
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 24 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 24 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 255)))))))))))))))))))))))) (allB_succ 23 255 (allA_succ_of_accept 22 23
  255 (accept_3_4 22 23 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 255
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 23 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 255 (accept_3_4 19 23 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 255 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 23 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 17
  23 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 255 (accept_3_4 16 23
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 23 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 255 (accept_3_4 13 23 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 11
  23 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 255 (accept_3_4 10 23
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 255
  (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 255 (accept_3_4 7 23 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 23 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 5
  23 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 255 (accept_3_4 4 23 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 255 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3
  23 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 255 (accept_3_4 1 23 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  255))))))))))))))))))))))) (allB_succ 22 255 (allA_succ_of_accept 21 22 255 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 22 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 255 (accept_3_5 20
  22 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 22 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 22 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 255 (accept_3_5 17 22 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 22 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 22 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 255 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  22 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 255 (accept_3_5 14 22
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 22 255 (Polychromatic418967fa.accept_4_1_2_3_1_9
  13 22 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 255
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 22 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 22 255 (accept_3_5 11 22 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  22 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 22 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 22 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 255 (accept_3_5 8 22 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 22 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 255
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 22 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 22 255 (accept_3_5 5 22 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22
  255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 22 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 22 255 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 22 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 255 (accept_3_5 2 22 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 22 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 255)))))))))))))))))))))) (allB_succ 21 255 (allA_succ_of_accept
  20 21 255 (Polychromatic418967fa.accept_16_4_5_15_1_5083 20 21 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 21 255 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 21 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 255 3 6 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  21 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 255
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 21 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 255 3 5 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 21 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 255 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 21 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 255 3 4 7 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 255
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 21 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 255 3 3 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 255 (Polychromatic418967fa.accept_22_8_21_13_1_15543 8 21 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 255
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 21 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 21 255 3 2 7 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 21 255 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 21 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 255 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 21 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 255 3 1 7 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 255 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 21 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 21 255))))))))))))))))))))) (allB_succ 20 255 (allA_succ_of_accept 19 20 255
  (accept_3_4 19 20 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 255
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 20 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 255 (accept_3_4 16 20 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 20 255 5 3 4 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 20 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 20 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 255 (accept_3_4 13 20 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 255 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 20 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 20 255 5 2 4 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 20 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 20 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 255 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 20 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 255 (accept_3_4 7 20 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 255 (Polychromatic418967fa.accept_9_6_2_3_1_771 6
  20 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 20 255 5 1 4 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 20 255 (accept_3_4 4 20
  255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20 255 (Polychromatic418967fa.accept_8_3_4_7_1_475
  3 20 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 255
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 20 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 20 255 (accept_3_4 1 20 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  255)))))))))))))))))))) (allB_succ 19 255 (allA_succ_of_accept 18 19 255
  (Polychromatic418967fa.accept_16_2_3_15_1_6309 18 19 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 255 (accept_3_5 17 19 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 255 (accept_3_5 14 19 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 19 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 255
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 19 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 255 (accept_3_5 11 19 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 255 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 255 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 19 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 255 (accept_3_5 8 19 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 255 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 19 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 19 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 255 (accept_3_5 5 19 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 255 (Polychromatic418967fa.accept_27_3_19_12_1_15542 3 19 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 255 (accept_3_5 2 19 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 255))))))))))))))))))) (allB_succ 18 255 (allA_succ_of_accept 17
  18 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 255 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 18 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 255 3 5 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 255 (Polychromatic418967fa.accept_12_2_6_3_1_331 14
  18 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 255 3 4 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 255 (Polychromatic418967fa.accept_19_11_18_8_1_5911 11 18 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 255 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 18 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 255 3 3 6 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 255
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 18 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 255 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 18 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 255 3 2 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 255
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 18 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 255 3 1 6 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 255 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 18 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 255)))))))))))))))))) (allB_succ 17 255
  (allA_succ_of_accept 16 17 255 (accept_3_4 16 17 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 17 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 255 (accept_3_4 13 17 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 255 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 17 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 255
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 17 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 255 (accept_3_4 10 17 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 255 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 17 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 255 (accept_3_4 7 17 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 255
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 17 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 255 (accept_3_4 4 17 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 17 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 255 (accept_3_4 1 17 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 255))))))))))))))))) (allB_succ 16 255 (allA_succ_of_accept 15 16 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 255 (accept_3_5 14 16 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 255 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 16 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 255 (accept_3_5 11 16 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 16 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 255
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 16 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 255 (accept_3_5 8 16 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 255 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 16 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 255 (accept_3_5 5 16 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 255 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 16 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 255
  (Polychromatic418967fa.accept_22_3_16_13_1_15541 3 16 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 16 255 (accept_3_5 2 16 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16
  255 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 16 255)))))))))))))))) (allB_succ 15 255 (allA_succ_of_accept 14 15 255
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 15 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 255 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 15 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 255 3 4 5 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 15 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 255 5 2 3 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 15 255 3 3 5 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 255
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 15 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 255 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 15 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 255 3 2 5 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 15 255 5 1 3 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 15 255 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 255 3 1 5 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 255
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 15 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 255 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 15 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 255))))))))))))))) (allB_succ 14 255 (allA_succ_of_accept 13 14 255
  (accept_3_4 13 14 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 255
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 14 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 255 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 255 (accept_3_4 10 14 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 255 (Polychromatic418967fa.accept_9_8_5_3_1_777 8
  14 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 255 (accept_3_4 7 14 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 255 (Polychromatic418967fa.accept_9_6_5_3_1_205 6
  14 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 255 (accept_3_4 4 14 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  255 (Polychromatic418967fa.accept_19_3_14_8_1_3272 3 14 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 14 255 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 14 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 255 (accept_3_4 1 14 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 14 255)))))))))))))) (allB_succ 13 255 (allA_succ_of_accept 12 13 255
  (Polychromatic418967fa.accept_10_2_3_5_1_996 12 13 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 255 (accept_3_5 11 13 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 255 (accept_3_5 8 13 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 255 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 13 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 255
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 255 (accept_3_5 5 13 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  255 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 255 (Polychromatic418967fa.accept_16_3_13_15_1_1913 3 13 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 255 (accept_3_5 2 13 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 255 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 13 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 255))))))))))))) (allB_succ 12 255 (allA_succ_of_accept 11 12
  255 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 12 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 255 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 12 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 255 3 3 4 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 12 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 255
  (Polychromatic418967fa.accept_10_7_2_5_1_298 7 12 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 255 3 2 4 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 255 (Polychromatic418967fa.accept_13_5_12_8_1_198 5 12 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 255 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 12 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 255 3 1 4 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 255
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 12 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 255 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 255)))))))))))) (allB_succ 11 255 (allA_succ_of_accept 10 11 255
  (accept_3_4 10 11 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 255
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 11 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 255 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 255 (accept_3_4 7 11 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 255 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 11 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 255 (Polychromatic418967fa.accept_9_5_2_3_1_194 5
  11 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 255 (accept_3_4 4 11 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 255 (Polychromatic418967fa.accept_13_3_11_8_1_1094
  3 11 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 255
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 255 (accept_3_4 1 11 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  255))))))))))) (allB_succ 10 255 (allA_succ_of_accept 9 10 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 255 (accept_3_5 8 10 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 255 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 255
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 10 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 10 255 5 1 2 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 10 255 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 10 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 255 (Polychromatic418967fa.accept_20_3_10_15_1_620 3 10 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 255 (accept_3_5 2 10 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 255 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 10
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 255)))))))))) (allB_succ 9 255
  (allA_succ_of_accept 8 9 255 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 9 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 255 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 9 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 255 3 2 3 85 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 255
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 255 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 9 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 255 3 1 3 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 255
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 255))))))))) (allB_succ 8 255 (allA_succ_of_accept 7 8 255 (accept_3_4 7 8 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 255 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 8 255 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 255
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 255 (accept_3_4 4 8 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 255
  (Polychromatic418967fa.accept_10_3_8_5_1_606 3 8 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 255 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 8 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 255 (accept_3_4 1 8 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 255)))))))) (allB_succ 7 255 (allA_succ_of_accept 6 7 255
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 7 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 255 (accept_3_5 5 7 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 255
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 255 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 7 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 255 (accept_3_5 2 7 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 255 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 7 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 255))))))) (allB_succ 6 255 (allA_succ_of_accept 5 6 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 255 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 6 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 255 3 1 2 85 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 255 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 6 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 255
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 255)))))) (allB_succ 5 255 (allA_succ_of_accept 4 5 255 (accept_3_4 4 5 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 255 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 5 255 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 255 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5
  255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 255 (accept_3_4 1 5 255
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 255))))) (allB_succ 4 255 (allA_succ_of_accept 3 4 255
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 4 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 255 (accept_3_5 2 4 255 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 255
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 255)))) (allB_succ 3 255 (allA_succ_of_accept 2 3 255 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 3 255
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 255
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 3 255 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 255))) (allB_succ 2 255 (allA_succ_of_accept 1 2 255 (accept_3_4 1 2 255 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 255)) (allB_two
  255))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


