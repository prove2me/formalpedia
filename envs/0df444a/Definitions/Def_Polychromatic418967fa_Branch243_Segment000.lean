-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch243_Segment000
-- name    : Polychromatic418967fa_Branch243_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:38:50.045194+00:00
-- url     : https://prove2.me/theorems/eb2bd86b-ccd4-4864-aba6-249527b178b6
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

def Polychromatic418967fa.branch_243_segment_000 : allB 100 243 :=
  allB_succ 99 243 (allA_succ_of_accept 98 99 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 98 99 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 97 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 243 3 32 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 94 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 243 3 31 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 243
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 92 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 243 (Polychromatic418967fa.accept_21_7_15_12_1_4008 91 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 243 9 10 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 243 (Polychromatic418967fa.accept_13_11_8_9_1_1161
  89 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 88 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 243 3 29 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 86 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 85 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 243 3 28 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 83 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 243 (Polychromatic418967fa.accept_13_4_8_9_1_1156 82 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 243 9 9 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 80 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 243
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 79 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 243 3 26 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 77 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 243 3 25 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 73 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 243 9 8 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 243 (Polychromatic418967fa.accept_19_14_4_15_1_2434 71 99
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 243
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 70 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 243 3 23 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 68 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 243 3 22 33 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 243
  (Polychromatic418967fa.accept_15_5_9_3_1_528 65 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 64 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 243 9 7 11 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 62 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 243
  (Polychromatic418967fa.accept_17_10_14_5_1_11167 61 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 99 243 3 20 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 99 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 99 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 243
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 58 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 99 243 3 19 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 99 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 56 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 99 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 243 9 6 11 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 99 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 99 243 3 17 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 99 243 (Polychromatic418967fa.accept_13_11_8_9_1_1161
  50 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 243
  (Polychromatic418967fa.accept_19_11_4_15_1_5052 49 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 99 243 3 16 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 99 243 (Polychromatic418967fa.accept_19_9_4_15_1_1415 47 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 243 9 5 11 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 243
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 44 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 243 (Polychromatic418967fa.accept_13_4_8_9_1_1156 43 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 99 243 3 14 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 99 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 41
  99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 243
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 40 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 99 243 3 13 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 99 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 243 (Polychromatic418967fa.accept_13_11_8_9_1_1161 37 99
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 243 9 4 11 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 243
  (Polychromatic418967fa.accept_15_5_9_3_1_528 35 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 99 243 3 11 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 99 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 32
  99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 99 243 3 10 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 99 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 29 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 243 (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 99
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 243 9 3 11 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 243
  (Polychromatic418967fa.accept_10_6_9_3_1_935 26 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 99 243 3 8 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 99 243 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 243
  (Polychromatic418967fa.accept_20_2_19_3_1_10530 22 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 99 243 3 7 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 99 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 243 (Polychromatic418967fa.accept_17_2_14_5_1_2575 19 99
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 243 9 2 11 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 99 243 3 5 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 99 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 99 243 3 4 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 99 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 243 9 1 11 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 243
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 99 243 3 2 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 99 243 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 99 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 99 243 3 1 33 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 99 243 (Polychromatic418967fa.accept_17_2_14_5_1_2575 2 99 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 243 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 99 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  243 (allA_succ_of_accept 97 98 243 (accept_3_4 97 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 96 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 95 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 243 (accept_3_4 94 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 243
  (Polychromatic418967fa.accept_19_16_3_15_1_14603 92 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 98 243 (accept_3_4 91 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 98 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 90 98 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 98 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 243 (accept_3_4 88 98 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995
  87 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 86 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 243 (accept_3_4 85 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 243 (Polychromatic418967fa.accept_13_6_7_9_1_1848 84 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 243 (accept_3_4 82 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 243
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 80 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 243 (accept_3_4 79 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 78 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 243 (accept_3_4 76 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 75 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 243
  (Polychromatic418967fa.accept_19_17_3_15_1_9284 74 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 243 (accept_3_4 73 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995 72 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 243 (accept_3_4 70 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 243
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 68 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 243 (accept_3_4 67 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 66 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 243 (accept_3_4 64 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 243 (Polychromatic418967fa.accept_13_11_7_9_1_612 63 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 243
  (Polychromatic418967fa.accept_20_2_18_3_1_4519 62 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 243 (accept_3_4 61 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 243 (Polychromatic418967fa.accept_13_8_7_9_1_611 60 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 243 (accept_3_4 58 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 243 (accept_3_4 55 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 243 (accept_3_4 52 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 243
  (Polychromatic418967fa.accept_13_11_7_9_1_612 50 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 243 (accept_3_4 49 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 243 (Polychromatic418967fa.accept_19_10_3_15_1_13355 48 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 243 (accept_3_4 46 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 243
  (Polychromatic418967fa.accept_17_10_13_5_1_3513 44 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 243 (accept_3_4 43 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 243 (accept_3_4 40 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 243 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 243
  (Polychromatic418967fa.accept_16_6_2_3_1_4223 38 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 243 (accept_3_4 37 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 243 (accept_3_4 34 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 243
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 32 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 243 (accept_3_4 31 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 243 (accept_3_4 28 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 243 (accept_3_4 25 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 243 (accept_3_4 22 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 243
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 243 (accept_3_4 19 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 243 (accept_3_4 16 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 98 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 243
  (Polychromatic418967fa.accept_22_14_10_1_1_14643 14 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 98 243 (accept_3_4 13 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 98 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 98 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 98 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 243 (accept_3_4 10 98 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 98
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 243
  (Polychromatic418967fa.accept_13_8_7_9_1_611 8 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 243 (accept_3_4 7 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  243 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 98 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 243 (accept_3_4 4 98 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 98 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  2 98 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 243 (accept_3_4 1 98
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  243 (allA_succ_of_accept 96 97 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 96 97 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 243 (accept_3_5 95 97 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 243 (Polychromatic418967fa.accept_12_9_1_3_1_350
  93 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 243 (accept_3_5 92
  97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 243
  (Polychromatic418967fa.accept_22_3_9_1_1_6771 91 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 97 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 243 (accept_3_5 89 97 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 97 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186
  87 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 243 (accept_3_5 86
  97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 85 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 97 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 84 97 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 243 (accept_3_5 83 97 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 81
  97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 243 (accept_3_5 80 97
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 243
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 79 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 97 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 243 (accept_3_5 77 97 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 97 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 243 (Polychromatic418967fa.accept_10_5_7_3_1_561
  75 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 243 (accept_3_5 74
  97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 243
  (Polychromatic418967fa.accept_36_1_25_27_1_14642 73 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 243 (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 243 (accept_3_5 71 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 69 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 243 (accept_3_5 68 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 243 (accept_3_5 65 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 243
  (Polychromatic418967fa.accept_19_6_2_15_1_9266 63 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 243 (accept_3_5 62 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 243 (Polychromatic418967fa.accept_16_13_1_3_1_2205 61 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 243 (accept_3_5 59 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 243 (accept_3_5 56 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 243 (accept_3_5 53 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 243
  (Polychromatic418967fa.accept_19_13_2_15_1_7920 51 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 243 (accept_3_5 50 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 243 (Polychromatic418967fa.accept_13_10_6_9_1_1152 49 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 243 (Polychromatic418967fa.accept_14_6_13_5_1_534 48 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 243 (accept_3_5 47 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 243 (accept_3_5 44 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 243 (accept_3_5 41 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 243 (accept_3_5 38 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 243 (Polychromatic418967fa.accept_19_18_2_15_1_3718 37 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 243 (accept_3_5 35 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 243 (accept_3_5 32 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 243 (Polychromatic418967fa.accept_23_8_5_13_1_14641 31 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 243 (accept_3_5 29 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 243
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 243 (accept_3_5 26 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 243 (accept_3_5 23 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 243
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 243 (accept_3_5 20 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 243 (Polychromatic418967fa.accept_15_4_7_3_1_119 19 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 243 (accept_3_5 17 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 243 (accept_3_5 14 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 243 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 243 (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 243 (accept_3_5 11 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 97 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 243 (accept_3_5 8 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  243 (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 243 (accept_3_5 5 97 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 243
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 243 (accept_3_5 2 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  243 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 96 243 (allA_succ_of_accept 95 96 243 (Polychromatic418967fa.accept_13_4_5_9_1_1829 95 96 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 243
  (Polychromatic418967fa.accept_13_3_5_9_1_5285 94 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 96 243 3 31 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 92 96 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 92 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 243 (Polychromatic418967fa.accept_14_7_12_5_1_1861 91 96
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 243 3 30 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 243
  (Polychromatic418967fa.accept_10_9_6_3_1_545 89 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 88 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 96 243 3 29 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 96 243 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  86 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 243
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 85 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 243 3 28 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 243 (Polychromatic418967fa.accept_17_15_11_5_1_9866 83 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 96 243 (Polychromatic418967fa.accept_13_4_5_9_1_1829 82 96 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 243 3 27 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 243
  (Polychromatic418967fa.accept_13_2_5_9_1_610 80 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 96 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 79 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 243 3 26 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 243 (Polychromatic418967fa.accept_10_7_6_3_1_927 77
  96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 243
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 76 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 96 243 3 25 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 96 243 (Polychromatic418967fa.accept_17_6_11_5_1_3506 74 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 243 (Polychromatic418967fa.accept_14_3_12_5_1_153 73 96 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 243 3 24 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 243
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 71 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 70 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 96 243 3 23 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 96 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  68 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 243
  (Polychromatic418967fa.accept_10_7_6_3_1_927 67 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 243 3 22 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 96 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 65 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 243 (Polychromatic418967fa.accept_22_20_8_1_1_6734 64 96
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 243 3 21 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 243
  (Polychromatic418967fa.accept_18_8_6_9_1_5576 62 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 96 243 (Polychromatic418967fa.accept_15_1_6_3_1_2827 61 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 243 3 20 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 59
  96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 96 243 3 19 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 96 243 (Polychromatic418967fa.accept_13_4_5_9_1_1829 56 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 55 96 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 243 3 18 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 243
  (Polychromatic418967fa.accept_13_1_5_9_1_226 53 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 243 (Polychromatic418967fa.accept_14_10_12_5_1_3466 52 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 96 243 3 17 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 96 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 50
  96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 243
  (Polychromatic418967fa.accept_10_9_6_3_1_545 49 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 243 3 16 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 243 (Polychromatic418967fa.accept_10_7_6_3_1_927 47 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 243 (Polychromatic418967fa.accept_15_1_6_3_1_2827 46 96 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 243 3 15 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 243
  (Polychromatic418967fa.accept_18_8_6_9_1_5576 44 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 243 (Polychromatic418967fa.accept_13_4_5_9_1_1829 43 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 243 3 14 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 41
  96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 243
  (Polychromatic418967fa.accept_13_1_5_9_1_226 40 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 96 243 3 13 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 96 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 243 (Polychromatic418967fa.accept_10_7_6_3_1_927 37 96 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 243 3 12 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 243
  (Polychromatic418967fa.accept_14_7_12_5_1_1861 35 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 243 (Polychromatic418967fa.accept_22_12_8_1_1_5108 34 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 96 243 3 11 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 96 243 (Polychromatic418967fa.accept_17_15_11_5_1_9866
  32 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 243
  (Polychromatic418967fa.accept_14_3_12_5_1_153 31 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 243 3 10 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 96 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 96 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 243 3 9 32 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 243
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 243 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 243 3 8 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 243 (Polychromatic418967fa.accept_17_6_11_5_1_3506 23 96 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 243
  (Polychromatic418967fa.accept_25_22_21_18_1_14640 22 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 96 243 3 7 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 96 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 20 96 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 243 (Polychromatic418967fa.accept_10_9_6_3_1_545
  19 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 243 3 6 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 243
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 16 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 96 243 3 5 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 243 (Polychromatic418967fa.accept_13_1_5_9_1_226 14 96 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 243
  (Polychromatic418967fa.accept_18_13_6_9_1_4280 13 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 243 3 4 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 243 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 243 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 96
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 243 3 3 32 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 243 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 243 3 2 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 96 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 243
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 96 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 96 243 3 1 32 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 96 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 2 96 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 243 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 96 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 243
  (allA_succ_of_accept 94 95 243 (accept_3_4 94 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 93 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 243 (accept_3_4 91 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 243
  (Polychromatic418967fa.accept_20_9_15_3_1_7470 89 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 243 (accept_3_4 88 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 87 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 243 (accept_3_4 85 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 84 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 83 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 243 (accept_3_4 82 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 81 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 243 (accept_3_4 79 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 77 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 243 (accept_3_4 76 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 243 (Polychromatic418967fa.accept_16_11_15_3_1_1304 75 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 243 (accept_3_4 73 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 71 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 243 (accept_3_4 70 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 243 (accept_3_4 67 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 66 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 65 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 243 (accept_3_4 64 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 243 (Polychromatic418967fa.accept_17_12_10_5_1_4756 63 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 243 (accept_3_4 61 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 243
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 59 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 243 (accept_3_4 58 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 243 (accept_3_4 55 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 54 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 243
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 53 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 243 (accept_3_4 52 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 243 (accept_3_4 49 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 243 (accept_3_4 46 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 243 (accept_3_4 43 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 243 (accept_3_4 40 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 243 (accept_3_4 37 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 243
  (Polychromatic418967fa.accept_21_14_11_12_1_10182 35 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 95 243 (accept_3_4 34 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 95 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 95 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 243 (accept_3_4 31 95 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 30
  95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 243 (accept_3_4 28 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 243 (accept_3_4 25 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 243 (accept_3_4 22 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 243 (accept_3_4 19 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 243 (accept_3_4 16 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 243 (accept_3_4 13 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 243
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 243 (accept_3_4 10 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 243 (accept_3_4 7 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 95 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 243
  (Polychromatic418967fa.accept_13_5_4_9_1_601 5 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 243 (accept_3_4 4 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  243 (Polychromatic418967fa.accept_21_3_11_12_1_10183 3 95 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 95 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 243 (accept_3_4 1 95 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 95
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 243
  (allA_succ_of_accept 93 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 94 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 243 (accept_3_5 92 94 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  90 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 243 (accept_3_5 89
  94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 243
  (Polychromatic418967fa.accept_19_12_18_15_1_10690 88 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 94 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 87 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 243 (accept_3_5 86 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 243
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 84 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 94 243 (accept_3_5 83 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  94 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 82 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 94 243 (accept_3_5 80 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 94 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 94 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 78 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 94 243 (accept_3_5 77 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  94 243 (Polychromatic418967fa.accept_15_1_4_3_1_1928 76 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 94 243 (Polychromatic418967fa.accept_16_11_14_3_1_3140 75 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 243 (accept_3_5 74 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 94 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 94 243 (accept_3_5 71 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  94 243 (Polychromatic418967fa.accept_13_5_3_9_1_1189 70 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 243 (accept_3_5 68 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 94 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 94 243 (accept_3_5 65 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  94 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 94 243 (Polychromatic418967fa.accept_17_12_9_5_1_799 63 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 243 (accept_3_5 62 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 243
  (Polychromatic418967fa.accept_11_5_6_1_1_988 60 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 94 243 (accept_3_5 59 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  94 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 94 243 (accept_3_5 56 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 94 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 94 243 (accept_3_5 53 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  94 243 (Polychromatic418967fa.accept_15_7_4_3_1_1930 52 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 94 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 243 (accept_3_5 50 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 243
  (Polychromatic418967fa.accept_17_14_9_5_1_4755 48 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 94 243 (accept_3_5 47 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  94 243 (Polychromatic418967fa.accept_13_7_3_9_1_1142 46 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 243 (accept_3_5 44 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 243 (accept_3_5 41 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 243 (accept_3_5 38 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 243 (accept_3_5 35 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 243 (Polychromatic418967fa.accept_13_8_3_9_1_5269 34 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 243 (accept_3_5 32 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 243 (accept_3_5 29 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 243 (Polychromatic418967fa.accept_13_2_3_9_1_2610 28 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 243 (accept_3_5 26 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 243
  (Polychromatic418967fa.accept_17_7_9_5_1_2588 24 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 243 (accept_3_5 23 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 243 (accept_3_5 20 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 243
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 243 (accept_3_5 17 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 243 (accept_3_5 14 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 243
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 243 (accept_3_5 11 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 243 (Polychromatic418967fa.accept_26_10_16_9_1_14639 10 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 243 (accept_3_5 8 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 243 (accept_3_5 5 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  243 (Polychromatic418967fa.accept_19_4_18_15_1_7899 4 94 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 94 243 (Polychromatic418967fa.accept_19_3_18_15_1_3711 3 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 243 (accept_3_5 2 94 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 94 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 243
  (allA_succ_of_accept 92 93 243 (Polychromatic418967fa.accept_13_1_2_9_1_1186 92 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 91 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 243 3 30 31 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 89 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 88 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 243 3 29 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 86
  93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 85 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 243 3 28 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 83 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 243 3 27 31 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 79 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 243 3 26 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 77
  93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 243
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 76 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 243 3 25 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 73 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 243 3 24 31 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 71 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 243 3 23 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187
  68 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 67 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 243 3 22 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 243 (Polychromatic418967fa.accept_17_13_8_5_1_3532 64 93
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 243 3 21 31 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 61 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 243 3 20 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 59
  93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 243 3 19 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 243 (Polychromatic418967fa.accept_16_8_13_3_1_4253 56 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 55 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 243 3 18 31 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 243 3 17 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 243 3 16 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 47 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 243 3 15 31 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 243
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 44 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 243 3 14 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 41
  93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 243
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 40 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 243 3 13 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 243 3 12 31 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 35 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 243 3 11 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 32
  93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 243 3 10 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 243 3 9 31 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 243 3 8 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 243 3 7 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 243 (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 243 3 6 31 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 16 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 243 3 5 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 243 3 4 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 243 3 3 31 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 243
  (Polychromatic418967fa.accept_16_8_13_3_1_4253 8 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 243 3 2 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 93 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 243 3 1 31 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 93 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 93 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 243
  (allA_succ_of_accept 91 92 243 (accept_3_4 91 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 243 (accept_3_4 88 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 243
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 86 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 243 (accept_3_4 85 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 243 (Polychromatic418967fa.accept_13_6_1_9_1_619 84 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 243 (accept_3_4 82 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 243 (accept_3_4 79 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 243 (accept_3_4 76 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 75 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 243 (accept_3_4 73 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 243 (Polychromatic418967fa.accept_15_12_2_3_1_1146 72 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 243 (accept_3_4 70 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 243
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 68 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 243 (accept_3_4 67 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 243 (accept_3_4 64 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 243 (accept_3_4 61 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 243 (accept_3_4 58 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 243 (Polychromatic418967fa.accept_13_5_1_9_1_618 57 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 243
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 56 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 243 (accept_3_4 55 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 243 (accept_3_4 52 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 243
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 50 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 243 (accept_3_4 49 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 243 (accept_3_4 46 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 243
  (Polychromatic418967fa.accept_13_5_1_9_1_618 44 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 243 (accept_3_4 43 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 243 (accept_3_4 40 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 243 (accept_3_4 37 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 243 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 243 (accept_3_4 34 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 243 (Polychromatic418967fa.accept_20_13_12_3_1_5972 33 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 243 (accept_3_4 31 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 243 (accept_3_4 28 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 243
  (Polychromatic418967fa.accept_16_10_12_3_1_4252 26 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 243 (accept_3_4 25 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 243 (accept_3_4 22 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 243 (accept_3_4 19 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 243 (accept_3_4 16 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 243
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 243 (accept_3_4 13 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 243 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 243 (accept_3_4 10 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 243 (Polychromatic418967fa.accept_16_9_12_3_1_3138 9 92 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 243
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 243 (accept_3_4 7 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  243 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 243 (accept_3_4 4 92 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 92 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 243 (Polychromatic418967fa.accept_13_2_1_9_1_1174 2
  92 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 243 (accept_3_4 1 92 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 243
  (allA_succ_of_accept 90 91 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 90 91 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 243 (accept_3_5 89 91 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 243 (Polychromatic418967fa.accept_16_7_11_3_1_1330
  87 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 243 (accept_3_5 86
  91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 243
  (Polychromatic418967fa.accept_21_1_7_12_1_1465 85 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 243 (Polychromatic418967fa.accept_25_9_16_18_1_14638 84 91 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 243 (accept_3_5 83 91 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  81 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 243 (accept_3_5 80
  91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 243
  (Polychromatic418967fa.accept_11_2_3_1_1_244 79 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 91 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 78 91 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 243 (accept_3_5 77 91 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 243 (Polychromatic418967fa.accept_18_3_1_9_1_1929
  75 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 243 (accept_3_5 74
  91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 243
  (Polychromatic418967fa.accept_15_13_1_3_1_1972 73 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 91 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 91 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 243 (accept_3_5 71 91 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  69 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 243 (accept_3_5 68
  91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 243
  (Polychromatic418967fa.accept_21_4_7_12_1_10320 67 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 91 243 (Polychromatic418967fa.accept_15_6_1_3_1_2852 66 91 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 243 (accept_3_5 65 91 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 243
  (Polychromatic418967fa.accept_16_15_11_3_1_2179 63 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 91 243 (accept_3_5 62 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 243 (Polychromatic418967fa.accept_21_19_7_12_1_5507 61 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 243 (Polychromatic418967fa.accept_18_6_1_9_1_5551 60 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 243 (accept_3_5 59 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 243
  (Polychromatic418967fa.accept_11_2_3_1_1_244 57 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 243 (accept_3_5 56 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 243 (Polychromatic418967fa.accept_16_7_11_3_1_1330 55 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 243 (Polychromatic418967fa.accept_14_12_7_5_1_1107 54 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 243 (accept_3_5 53 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 91 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 243
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 51 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 243 (accept_3_5 50 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 243 (Polychromatic418967fa.accept_15_4_1_3_1_1922 49 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 243 (accept_3_5 47 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 243 (accept_3_5 44 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 243 (Polychromatic418967fa.accept_15_13_1_3_1_1972 43 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 243 (accept_3_5 41 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 243
  (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 243 (accept_3_5 38 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 243 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 243 (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 243 (accept_3_5 35 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 243 (accept_3_5 32 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 243 (Polychromatic418967fa.accept_16_15_11_3_1_2179 31 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 243 (Polychromatic418967fa.accept_14_2_7_5_1_5450 30 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 243 (accept_3_5 29 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 243
  (Polychromatic418967fa.accept_21_6_7_12_1_10136 27 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 243 (accept_3_5 26 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 243 (Polychromatic418967fa.accept_21_4_7_12_1_10320 25 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 243 (accept_3_5 23 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 243 (accept_3_5 20 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 243 (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 243 (accept_3_5 17 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 243
  (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 243 (accept_3_5 14 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 243 (accept_3_5 11 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 243 (accept_3_5 8 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  243 (Polychromatic418967fa.accept_16_7_11_3_1_1330 7 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 91 243 (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 243 (accept_3_5 5 91 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 243
  (Polychromatic418967fa.accept_17_3_6_5_1_8669 3 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 243 (accept_3_5 2 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  243 (Polychromatic418967fa.accept_17_1_6_5_1_3502 1 91 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 243
  (allA_succ_of_accept 89 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 88 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 243 3 29 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 86 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 243 3 28 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 243 (Polychromatic418967fa.accept_14_13_6_5_1_1853
  83 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 82 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 90 243 9 9 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 90 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 80 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 243 (Polychromatic418967fa.accept_20_19_10_3_1_13274 79 90
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 243 3 26 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 76 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 243 3 25 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 74
  90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 243 9 8 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 70 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 90 243 3 23 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 68 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 243 3 22 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 90
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 64 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 90 243 9 7 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 90 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 62 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 243 3 20 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 243
  (Polychromatic418967fa.accept_20_19_10_3_1_13274 59 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 90 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 58 90 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 90 243 3 19 30 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 90 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 90 243 (Polychromatic418967fa.accept_13_3_12_9_1_1193 55 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 243 9 6 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 90 243 3 17 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 90 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 243 3 16 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 243
  (Polychromatic418967fa.accept_11_3_2_1_1_994 47 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 90 243 9 5 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 90 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 243 3 14 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 90 243 3 13 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 243 9 4 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 243 (Polychromatic418967fa.accept_20_15_10_3_1_7465 35 90
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 90 243 3 11 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 90 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 243 (Polychromatic418967fa.accept_20_11_10_3_1_10529 31 90
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 243 3 10 30 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 90 243 9 3 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 90 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 243 3 8 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 243 (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 243 3 7 30 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 90 243 (Polychromatic418967fa.accept_20_19_10_3_1_13274 19 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 243 9 2 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 90 243 3 5 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 90 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 243 3 4 30 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 90 243 9 1 10 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 90 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 243
  (Polychromatic418967fa.accept_16_7_10_3_1_2210 7 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 243 3 2 30 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 90 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 243 3 1 30 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 90 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 90 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 243
  (allA_succ_of_accept 88 89 243 (accept_3_4 88 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 243 (Polychromatic418967fa.accept_16_7_9_3_1_1324 87 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 243 (accept_3_4 85 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 243
  (Polychromatic418967fa.accept_19_7_13_15_1_2407 83 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 243 (accept_3_4 82 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 243 (accept_3_4 79 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 243
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 77 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 243 (accept_3_4 76 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 243 (Polychromatic418967fa.accept_20_15_9_3_1_7435 75 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 243 (accept_3_4 73 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 243 (Polychromatic418967fa.accept_13_7_11_9_1_1858 72 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 243
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 71 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 243 (accept_3_4 70 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 243 (accept_3_4 67 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 243
  (Polychromatic418967fa.accept_32_1_25_19_1_14637 65 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 89 243 (accept_3_4 64 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 89 243 (Polychromatic418967fa.accept_19_6_13_15_1_2406 63 89 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 89 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 243 (accept_3_4 61 89 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 243 (Polychromatic418967fa.accept_13_8_11_9_1_593
  60 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 243
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 59 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 243 (accept_3_4 58 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 243 (accept_3_4 55 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 243
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 53 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 243 (accept_3_4 52 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 243 (Polychromatic418967fa.accept_18_15_17_9_1_4200 51 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 243 (accept_3_4 49 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 243 (Polychromatic418967fa.accept_18_12_17_9_1_5513 48 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 243
  (Polychromatic418967fa.accept_13_8_11_9_1_593 47 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 243 (accept_3_4 46 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 243 (accept_3_4 43 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 243
  (Polychromatic418967fa.accept_13_2_11_9_1_591 41 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 243 (accept_3_4 40 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 243 (Polychromatic418967fa.accept_16_7_9_3_1_1324 39 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 243 (accept_3_4 37 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 243
  (Polychromatic418967fa.accept_17_1_4_5_1_3501 35 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 243 (accept_3_4 34 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 243 (accept_3_4 31 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 243
  (Polychromatic418967fa.accept_21_8_5_12_1_10219 29 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 243 (accept_3_4 28 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 243 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 243 (accept_3_4 25 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 243
  (Polychromatic418967fa.accept_16_7_9_3_1_1324 23 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 243 (accept_3_4 22 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 243 (accept_3_4 19 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 243
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 243 (accept_3_4 16 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 243 (Polychromatic418967fa.accept_13_2_11_9_1_591 15 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 243 (accept_3_4 13 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 243 (Polychromatic418967fa.accept_16_12_9_3_1_5363 12 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 243
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 243 (accept_3_4 10 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 243 (accept_3_4 7 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 89 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 243
  (Polychromatic418967fa.accept_23_5_20_13_1_11447 5 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 243 (accept_3_4 4 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  243 (Polychromatic418967fa.accept_25_3_14_18_1_14636 3 89 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 89 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 243 (accept_3_4 1 89 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 89
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 243
  (allA_succ_of_accept 87 88 243 (Polychromatic418967fa.accept_15_12_13_3_1_1915 87 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 243 (accept_3_5 86 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 243 (Polychromatic418967fa.accept_13_6_10_9_1_4329
  84 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 243 (accept_3_5 83
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 243
  (Polychromatic418967fa.accept_19_6_12_15_1_7895 82 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 88 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 81 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 243 (accept_3_5 80 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 78
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 243 (accept_3_5 77 88
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 76 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 88 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 75 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 243 (accept_3_5 74 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 72
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 243 (accept_3_5 71 88
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 243
  (Polychromatic418967fa.accept_15_10_13_3_1_4816 70 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 88 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 243 (accept_3_5 68 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 243 (Polychromatic418967fa.accept_10_6_8_3_1_930
  66 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 243 (accept_3_5 65
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 64 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 88 243 (Polychromatic418967fa.accept_19_6_12_15_1_7895 63 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 243 (accept_3_5 62 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 243 (Polychromatic418967fa.accept_16_12_8_3_1_4241
  60 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 243 (accept_3_5 59
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 58 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 88 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 243 (accept_3_5 56 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 243 (Polychromatic418967fa.accept_12_6_4_3_1_361
  54 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 243 (accept_3_5 53
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 243
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 52 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 88 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 243 (accept_3_5 50 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 48
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 243 (accept_3_5 47 88
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 46 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 88 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 243 (accept_3_5 44 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 243 (Polychromatic418967fa.accept_12_6_4_3_1_361
  42 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 243 (accept_3_5 41
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 243
  (Polychromatic418967fa.accept_13_1_10_9_1_215 40 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 88 243 (Polychromatic418967fa.accept_15_9_13_3_1_535 39 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 243 (accept_3_5 38 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 36
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 243 (accept_3_5 35 88
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 88 243 (Polychromatic418967fa.accept_18_15_16_9_1_4299 33 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 243 (accept_3_5 32 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 30
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 243 (accept_3_5 29 88
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 243
  (Polychromatic418967fa.accept_16_12_8_3_1_4241 28 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 88 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 243 (accept_3_5 26 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 243 (Polychromatic418967fa.accept_15_9_13_3_1_535
  24 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 243 (accept_3_5 23
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 22 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 88 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 243 (accept_3_5 20 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 243 (Polychromatic418967fa.accept_12_6_4_3_1_361
  18 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 243 (accept_3_5 17
  88 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 88 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 243 (accept_3_5 14 88 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 243
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 243 (accept_3_5 11 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 243 (Polychromatic418967fa.accept_15_10_13_3_1_4816 10 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 243 (accept_3_5 8 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 243 (accept_3_5 5 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  243 (Polychromatic418967fa.accept_16_4_8_3_1_4206 4 88 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 88 243 (Polychromatic418967fa.accept_19_3_12_15_1_568 3 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 243 (accept_3_5 2 88 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 243
  (allA_succ_of_accept 86 87 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 86 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 85 87 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 243 3 28 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 243
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 83 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 243 (Polychromatic418967fa.accept_14_12_3_5_1_1868 82 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 243 3 27 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 243 (Polychromatic418967fa.accept_19_4_11_15_1_3743
  80 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 79 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 243 3 26 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 243 (Polychromatic418967fa.accept_15_2_12_3_1_1183 77 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 87 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 243 3 25 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 243
  (Polychromatic418967fa.accept_10_4_7_3_1_54 74 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 243 (Polychromatic418967fa.accept_15_13_12_3_1_1180 73 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 243 3 24 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 71
  87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 243
  (Polychromatic418967fa.accept_18_16_15_9_1_6852 70 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 243 3 23 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 68 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 243 (Polychromatic418967fa.accept_15_7_12_3_1_1137 67 87
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 243 3 22 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 243 3 21 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 243 (Polychromatic418967fa.accept_15_2_12_3_1_1183
  62 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 243
  (Polychromatic418967fa.accept_19_4_11_15_1_3743 61 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 243 3 20 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 243 (Polychromatic418967fa.accept_16_11_7_3_1_3163 59 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 87 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 243 3 19 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 243
  (Polychromatic418967fa.accept_10_6_7_3_1_547 56 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 243 3 18 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 243 (Polychromatic418967fa.accept_11_9_10_1_1_581
  53 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 52 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 243 3 17 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 243 (Polychromatic418967fa.accept_21_7_3_12_1_1455 49 87
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 243 3 16 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 243
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 47 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 46 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 243 3 15 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 44
  87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 243 3 14 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 243 (Polychromatic418967fa.accept_16_9_7_3_1_614 41 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 243 (Polychromatic418967fa.accept_14_12_3_5_1_1868 40 87
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 243 3 13 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 243
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 38 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 243 3 12 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 35
  87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 243
  (Polychromatic418967fa.accept_10_4_7_3_1_54 34 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 243 3 11 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 243 (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 87 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 243 3 10 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 243 3 9 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 87 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 25 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 243 3 8 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 87 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 243 3 7 29 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 20 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 243 (Polychromatic418967fa.accept_25_19_12_18_1_14635 19 87 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 243 3 6 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 243 (Polychromatic418967fa.accept_15_2_12_3_1_1183
  17 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 243 3 5 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 87
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 243 3 4 29 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 243
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 11 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 243 (Polychromatic418967fa.accept_16_10_7_3_1_6601 10 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 243 3 3 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 87 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 243
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 243 3 2 29 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 87 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 243 3 1 29 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 87 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 87 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 243
  (allA_succ_of_accept 85 86 243 (accept_3_4 85 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 243 (Polychromatic418967fa.accept_16_4_6_3_1_1311 84 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 243 (accept_3_4 82 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 243 (accept_3_4 79 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 78 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 243 (accept_3_4 76 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 243 (Polychromatic418967fa.accept_16_11_6_3_1_6564 75 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 243 (accept_3_4 73 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 72 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 243 (accept_3_4 70 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 68 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 243 (accept_3_4 67 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 243 (accept_3_4 64 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 243 (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 243
  (Polychromatic418967fa.accept_19_5_10_15_1_5076 62 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 243 (accept_3_4 61 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 243 (accept_3_4 58 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 243
  (Polychromatic418967fa.accept_13_4_8_9_1_1156 56 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 243 (accept_3_4 55 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 243 (accept_3_4 52 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 51 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 243
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 50 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 243 (accept_3_4 49 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 243 (accept_3_4 46 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 243
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 44 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 243 (accept_3_4 43 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 243 (accept_3_4 40 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 243 (accept_3_4 37 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 243 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 243 (accept_3_4 34 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 243 (accept_3_4 31 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 243 (accept_3_4 28 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 243 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 243
  (Polychromatic418967fa.accept_23_3_17_13_1_14634 26 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 86 243 (accept_3_4 25 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 86 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 86 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 86 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 86 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 243 (accept_3_4 22 86 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 243
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 20 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 243 (accept_3_4 19 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 243 (accept_3_4 16 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 243 (Polychromatic418967fa.accept_24_15_14_3_1_9615 15 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 243
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 243 (accept_3_4 13 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 243 (accept_3_4 10 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 86 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 243 (accept_3_4 7 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  243 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 86 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 243 (accept_3_4 4 86 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 86 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 243 (Polychromatic418967fa.accept_16_2_6_3_1_5396 2
  86 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 243 (accept_3_4 1 86 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 243
  (allA_succ_of_accept 84 85 243 (Polychromatic418967fa.accept_13_6_7_9_1_1848 84 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 243 (accept_3_5 83 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 81
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 243 (accept_3_5 80 85
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 243
  (Polychromatic418967fa.accept_19_3_9_15_1_9240 79 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 243 (accept_3_5 77 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 243 (Polychromatic418967fa.accept_18_3_13_9_1_4260
  75 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 243 (accept_3_5 74
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 73 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 85 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 243 (accept_3_5 71 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 69
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 243 (accept_3_5 68 85
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 67 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 243 (accept_3_5 65 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 85 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 243 (Polychromatic418967fa.accept_13_11_7_9_1_612
  63 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 243 (accept_3_5 62
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 243
  (Polychromatic418967fa.accept_19_4_9_15_1_6405 61 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 85 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 243 (accept_3_5 59 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 243 (Polychromatic418967fa.accept_10_7_5_3_1_542
  57 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 243 (accept_3_5 56
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 243 (accept_3_5 53 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 85 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 243 (Polychromatic418967fa.accept_15_6_10_3_1_2844
  51 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 243 (accept_3_5 50
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 243
  (Polychromatic418967fa.accept_19_11_9_15_1_5055 49 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 243 (accept_3_5 47 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 45
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 243 (accept_3_5 44 85
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 243
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 43 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 243 (accept_3_5 41 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 85 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 39
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 243 (accept_3_5 38 85
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 37 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 85 243 (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 243 (accept_3_5 35 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 243 (Polychromatic418967fa.accept_12_9_1_3_1_350
  33 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 243 (accept_3_5 32
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 243 (accept_3_5 29 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 85 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 27
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 243 (accept_3_5 26 85
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 25 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 85 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 243 (accept_3_5 23 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 243 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 243 (accept_3_5 20
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 243
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 19 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 243 (accept_3_5 17 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  15 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 243 (accept_3_5 14
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 85 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 243 (accept_3_5 11 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 85 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 243 (accept_3_5 8 85 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 7
  85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 243 (accept_3_5 5 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 243 (accept_3_5 2 85 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 243 (Polychromatic418967fa.accept_20_1_5_3_1_7397 1 85 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 243
  (allA_succ_of_accept 83 84 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 83 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 82 84 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 243 3 27 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 243
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 80 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 243 3 26 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 77
  84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 84 243
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 76 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 84 243 3 25 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 84 243 (Polychromatic418967fa.accept_19_17_8_15_1_6448 74 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 243 (Polychromatic418967fa.accept_15_13_9_3_1_1949 73 84
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 243 3 24 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 71 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 243 (Polychromatic418967fa.accept_15_10_9_3_1_1947 70 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 243 3 23 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 243 (Polychromatic418967fa.accept_13_3_6_9_1_1150
  68 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 243
  (Polychromatic418967fa.accept_10_7_4_3_1_560 67 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 243 3 22 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 243 (Polychromatic418967fa.accept_15_5_9_3_1_528 65 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 243 (Polychromatic418967fa.accept_18_10_12_9_1_2012 64 84
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84 243 3 21 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 84 243
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 62 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 84 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 61 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 243 3 20 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 59
  84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 243
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 58 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 84 243 3 19 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 84 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 56 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 84 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 243 3 18 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 243
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 53 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 243 (Polychromatic418967fa.accept_17_1_16_5_1_3670 52 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 243 3 17 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 50
  84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 243
  (Polychromatic418967fa.accept_10_9_4_3_1_539 49 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 243 3 16 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 243 (Polychromatic418967fa.accept_13_7_6_9_1_1831 46 84 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 243 3 15 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 243
  (Polychromatic418967fa.accept_16_12_4_3_1_4295 44 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 43 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 243 3 14 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 243 (Polychromatic418967fa.accept_13_2_6_9_1_2636
  41 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 243
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 84 243 3 13 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 84 243 (Polychromatic418967fa.accept_15_8_9_3_1_1194 38 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 84 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 243 3 12 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 243
  (Polychromatic418967fa.accept_15_5_9_3_1_528 35 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 243 (Polychromatic418967fa.accept_18_16_12_9_1_5504 34 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 243 3 11 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 243
  (Polychromatic418967fa.accept_29_3_26_11_1_14633 32 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 84 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 84 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 243 3 10 28 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 243
  (Polychromatic418967fa.accept_10_9_4_3_1_539 29 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 84 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 28 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 243 3 9 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 243 (Polychromatic418967fa.accept_19_7_8_15_1_2448 26 84 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 84 243
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 243 3 8 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 243 (Polychromatic418967fa.accept_16_6_4_3_1_2189 22 84 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 84 243 3 7 28 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 84 243
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 20 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 84 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 243 3 6 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 84 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 243
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 16 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 84 243 3 5 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 84 243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 243 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 84
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 243 3 4 28 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 243
  (Polychromatic418967fa.accept_17_11_16_5_1_3612 11 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 243 (Polychromatic418967fa.accept_13_10_6_9_1_1152 10 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 243 3 3 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 243 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 84 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 84 243 3 2 28 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 243 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 84 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 243 3 1 28 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 243
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 2 84 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 84 243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 84 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 84
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 243
  (allA_succ_of_accept 82 83 243 (accept_3_4 82 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 243 (accept_3_4 79 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 243
  (Polychromatic418967fa.accept_38_1_7_15_1_14632 77 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 243 (accept_3_4 76 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 243 (Polychromatic418967fa.accept_17_7_15_5_1_3649 75 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 243 (accept_3_4 73 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995 72 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 71 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 243 (accept_3_4 70 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 243 (accept_3_4 67 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 243 (Polychromatic418967fa.accept_13_1_5_9_1_226 66 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 243
  (Polychromatic418967fa.accept_15_5_8_3_1_556 65 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 243 (accept_3_4 64 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 243 (Polychromatic418967fa.accept_25_13_8_18_1_14631 63 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 243 (accept_3_4 61 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 243
  (Polychromatic418967fa.accept_25_9_8_18_1_14615 59 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 243 (accept_3_4 58 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 243 (accept_3_4 55 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 54 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 53 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 243 (accept_3_4 52 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 243 (accept_3_4 49 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 243 (Polychromatic418967fa.accept_14_6_13_5_1_534 48 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 243
  (Polychromatic418967fa.accept_17_13_15_5_1_3650 47 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 243 (accept_3_4 46 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 243 (accept_3_4 43 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 42 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 243
  (Polychromatic418967fa.accept_13_2_5_9_1_610 41 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 243 (accept_3_4 40 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 243 (accept_3_4 37 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 243
  (Polychromatic418967fa.accept_15_5_8_3_1_556 35 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 243 (accept_3_4 34 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 243 (accept_3_4 31 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 243 (Polychromatic418967fa.accept_13_4_5_9_1_1829 30 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 243 (accept_3_4 28 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 243 (accept_3_4 25 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 243 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 243
  (Polychromatic418967fa.accept_24_23_11_3_1_4226 23 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 243 (accept_3_4 22 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 243 (accept_3_4 19 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 243
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 17 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 243 (accept_3_4 16 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 243 (accept_3_4 13 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 243 (accept_3_4 10 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 243 (accept_3_4 7 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 243 (Polychromatic418967fa.accept_14_6_13_5_1_534 6 83 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 243
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 243 (accept_3_4 4 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 83 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 243 (accept_3_4 1 83 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 243
  (allA_succ_of_accept 81 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 82 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 243 (accept_3_5 80 82 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 82 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  78 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 243 (accept_3_5 77
  82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 243
  (Polychromatic418967fa.accept_29_18_24_11_1_14630 76 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 82 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 75 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 243 (accept_3_5 74 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 243
  (Polychromatic418967fa.accept_11_6_5_1_1_586 72 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 82 243 (accept_3_5 71 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  82 243 (Polychromatic418967fa.accept_13_5_4_9_1_601 70 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 243 (accept_3_5 68 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 82 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 82 243 (accept_3_5 65 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  82 243 (Polychromatic418967fa.accept_15_4_7_3_1_119 64 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 82 243 (Polychromatic418967fa.accept_14_7_12_5_1_1861 63 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 243 (accept_3_5 62 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 82 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 243
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 60 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 243 (accept_3_5 59 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 243 (Polychromatic418967fa.accept_13_6_4_9_1_4326 58 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 243 (accept_3_5 56 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 243 (accept_3_5 53 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 243 (Polychromatic418967fa.accept_14_10_12_5_1_3466 52 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 243 (accept_3_5 50 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 243
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 48 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 243 (accept_3_5 47 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 243 (Polychromatic418967fa.accept_13_7_4_9_1_1865 46 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 243 (accept_3_5 44 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 243 (accept_3_5 41 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 243 (Polychromatic418967fa.accept_15_10_7_3_1_1939 40 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 243 (accept_3_5 38 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 243
  (Polychromatic418967fa.accept_17_2_14_5_1_2575 36 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 243 (accept_3_5 35 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 243 (Polychromatic418967fa.accept_13_8_4_9_1_1145 34 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 243 (accept_3_5 32 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 243 (accept_3_5 29 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 243 (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 243 (accept_3_5 26 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 82 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 243
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 243 (accept_3_5 23 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 243 (Polychromatic418967fa.accept_16_6_2_3_1_4223 22 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 243 (accept_3_5 20 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 243 (accept_3_5 17 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 243 (Polychromatic418967fa.accept_19_16_6_15_1_2441 16 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 243 (accept_3_5 14 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 243
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 243 (accept_3_5 11 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 243 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 243 (accept_3_5 8 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 82 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 243
  (Polychromatic418967fa.accept_11_6_5_1_1_586 6 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 243 (accept_3_5 5 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  243 (Polychromatic418967fa.accept_15_4_7_3_1_119 4 82 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 243 (Polychromatic418967fa.accept_14_3_12_5_1_153 3 82 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 243 (accept_3_5 2 82 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 82 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 243
  (allA_succ_of_accept 80 81 243 (Polychromatic418967fa.accept_13_2_3_9_1_2610 80 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 79 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 243 3 26 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 77 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 76 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 243 3 25 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 73 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 243 9 8 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 243 3 23 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 243
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 68 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 67 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 243 3 22 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 65
  81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 64 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 243 9 7 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 243 3 20 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 59 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 243 3 19 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 243 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  56 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 243 27 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 52 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 243 3 17 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 243 3 16 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 243 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 243 9 5 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 243 3 14 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 243 (Polychromatic418967fa.accept_15_10_6_3_1_1160 40 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 243 3 13 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 243 9 4 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 243 3 11 27 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 243
  (Polychromatic418967fa.accept_10_2_1_3_1_233 32 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 243 3 10 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 243
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 243 27 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 243 3 8 27 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 243 3 7 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 243
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 243 9 2 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 243 3 5 27 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 243 3 4 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 243 9 1 9 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 243 3 2 27 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 243 (Polychromatic418967fa.accept_16_4_1_3_1_6581 4 81 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 243 3 1 27 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 81 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 81 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 243
  (allA_succ_of_accept 79 80 243 (accept_3_4 79 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 243 (accept_3_4 76 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 243 (Polychromatic418967fa.accept_17_7_12_5_1_1580 75 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 243
  (Polychromatic418967fa.accept_22_8_14_1_1_14629 74 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 243 (accept_3_4 73 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 243 (accept_3_4 70 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 69 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 243
  (Polychromatic418967fa.accept_11_2_3_1_1_244 68 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 243 (accept_3_4 67 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 243 (accept_3_4 64 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 243 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 243
  (Polychromatic418967fa.accept_15_2_5_3_1_552 62 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 243 (accept_3_4 61 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 243 (Polychromatic418967fa.accept_17_9_12_5_1_219 60 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 243 (accept_3_4 58 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 243
  (Polychromatic418967fa.accept_19_18_4_15_1_3721 56 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 243 (accept_3_4 55 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 243 (accept_3_4 52 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 243 (accept_3_4 49 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 243 (Polychromatic418967fa.accept_19_10_4_15_1_3720 48 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 243 (accept_3_4 46 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 243 (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 243 (accept_3_4 43 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 243 (accept_3_4 40 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 39 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 243
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 38 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 243 (accept_3_4 37 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 243 (accept_3_4 34 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 243 (Polychromatic418967fa.accept_13_7_2_9_1_1826 33 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 243
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 32 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 243 (accept_3_4 31 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 243 (accept_3_4 28 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 243 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 243
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 26 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 243 (accept_3_4 25 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 243 (accept_3_4 22 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 243
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 20 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 243 (accept_3_4 19 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 243 (accept_3_4 16 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 243
  (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 243 (accept_3_4 13 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 243 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 243 (accept_3_4 10 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 80 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 243 (accept_3_4 7 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  243 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 80 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 243 (accept_3_4 4 80 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 80 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 80
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 243 (accept_3_4 1 80 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 243
  (allA_succ_of_accept 78 79 243 (Polychromatic418967fa.accept_18_6_7_9_1_4250 78 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 243 (accept_3_5 77 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 243 (Polychromatic418967fa.accept_13_10_1_9_1_3380
  75 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 243 (accept_3_5 74
  79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 73 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 243 (Polychromatic418967fa.accept_21_9_16_12_1_4050 72 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 243 (accept_3_5 71 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 243 (Polychromatic418967fa.accept_11_3_2_1_1_994
  69 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 243 (accept_3_5 68
  79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 67 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 79 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 243 (accept_3_5 65 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 243 (Polychromatic418967fa.accept_13_11_1_9_1_1179
  63 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 243 (accept_3_5 62
  79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 243
  (Polychromatic418967fa.accept_15_1_4_3_1_1928 61 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 79 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 243 (accept_3_5 59 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  57 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 243 (accept_3_5 56
  79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 243
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 55 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 79 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 243 (accept_3_5 53 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 243
  (Polychromatic418967fa.accept_21_9_16_12_1_4050 51 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 243 (accept_3_5 50 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 243 (Polychromatic418967fa.accept_13_10_1_9_1_3380 49 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 243 (Polychromatic418967fa.accept_19_10_3_15_1_13355 48 79 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 243 (accept_3_5 47 79 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 79 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 243 (accept_3_5 44 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 243 (Polychromatic418967fa.accept_18_6_7_9_1_4250 42 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 243 (accept_3_5 41 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 243 (accept_3_5 38 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 243 (Polychromatic418967fa.accept_13_11_1_9_1_1179 37 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 243 (accept_3_5 35 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 79 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 243 (accept_3_5 32 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 243 (Polychromatic418967fa.accept_20_10_19_3_1_11807 30 79 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 243 (accept_3_5 29 79 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 243
  (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 243 (accept_3_5 26 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 243 (accept_3_5 23 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 79 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 243
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 243 (accept_3_5 20 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 243 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 243 (accept_3_5 17 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 243
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 15 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 243 (accept_3_5 14 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 243 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 243 (accept_3_5 11 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 79 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 243 (accept_3_5 8 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  243 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 79 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 243 (accept_3_5 5 79 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 79 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 243 (accept_3_5 2 79 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 243 (Polychromatic418967fa.accept_15_1_4_3_1_1928 1
  79 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 243
  (allA_succ_of_accept 77 78 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 76 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 243 3 25 26 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 243 3 24 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 71
  78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 70 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 243 3 23 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 68 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 67 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 243 3 22 26 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 64 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 243 3 21 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 62
  78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 243 3 20 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 58 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 243 3 19 26 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 243 3 18 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 78
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 52 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 243 3 17 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 50 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 243 3 16 26 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 243
  (Polychromatic418967fa.accept_17_13_10_5_1_2566 47 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 243 3 15 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 44
  78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 243
  (Polychromatic418967fa.accept_16_11_14_3_1_3140 43 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 243 3 14 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 243 3 13 26 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 243 3 12 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 35
  78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 34 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 243 3 11 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 243 3 10 26 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 243 3 9 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 243 3 8 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 243 (Polychromatic418967fa.accept_25_23_3_18_1_14628 23 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 243 3 7 26 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 243 (Polychromatic418967fa.accept_18_1_6_9_1_2001 19 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 243 3 6 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 16 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 243 3 5 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 243 3 4 26 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 243 3 3 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 243
  (Polychromatic418967fa.accept_18_7_6_9_1_4205 7 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 243 3 2 26 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 78 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 243 3 1 26 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 78 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 78 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 243
  (allA_succ_of_accept 76 77 243 (accept_3_4 76 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 243 (accept_3_4 73 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 243 (Polychromatic418967fa.accept_14_2_7_5_1_5450 72 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 243
  (Polychromatic418967fa.accept_19_14_1_15_1_7914 71 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 243 (accept_3_4 70 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 243 (accept_3_4 67 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 65 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 243 (accept_3_4 64 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 243 (Polychromatic418967fa.accept_16_15_13_3_1_4215 63 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 243 (accept_3_4 61 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 243 (Polychromatic418967fa.accept_13_8_12_9_1_1168 60 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 243
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 59 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 243 (accept_3_4 58 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 243 (accept_3_4 55 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 243
  (Polychromatic418967fa.accept_21_11_14_12_1_5471 53 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 77 243 (accept_3_4 52 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 77 243 (Polychromatic418967fa.accept_14_9_7_5_1_1105 51 77 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 77 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 243 (accept_3_4 49 77 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 243 (Polychromatic418967fa.accept_17_14_9_5_1_4755
  48 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 243
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 47 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 243 (accept_3_4 46 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 243 (accept_3_4 43 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 243
  (Polychromatic418967fa.accept_17_7_9_5_1_2588 41 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 243 (accept_3_4 40 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 243 (Polychromatic418967fa.accept_21_18_14_12_1_4075 39 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 243 (accept_3_4 37 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 243 (accept_3_4 34 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 243 (accept_3_4 31 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 243
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 29 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 243 (accept_3_4 28 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 243 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 243 (accept_3_4 25 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 243
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 243 (accept_3_4 22 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 243 (accept_3_4 19 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 243
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 17 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 243 (accept_3_4 16 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 243 (accept_3_4 13 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 243 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 243
  (Polychromatic418967fa.accept_19_11_1_15_1_9263 11 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 243 (accept_3_4 10 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 243 (accept_3_4 7 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 77 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 243 (accept_3_4 4 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  243 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 77 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 77 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 243 (accept_3_4 1 77 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 77 243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 76 243 (allA_succ_of_accept 75 76 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 75 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 243 (accept_3_5 74 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 243
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 72 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 243 (accept_3_5 71 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 243 (Polychromatic418967fa.accept_23_1_7_13_1_14627 70 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 69 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 243 (accept_3_5 68 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 66 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 243 (accept_3_5 65 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 243 (accept_3_5 62 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 243 (accept_3_5 59 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 243 (accept_3_5 56 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 54 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 243 (accept_3_5 53 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 243 (Polychromatic418967fa.accept_16_4_12_3_1_2180 52 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 243 (Polychromatic418967fa.accept_15_6_1_3_1_2852 51 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 243 (accept_3_5 50 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 243 (accept_3_5 47 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 243 (Polychromatic418967fa.accept_21_3_13_12_1_2653 45 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 243 (accept_3_5 44 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 243
  (Polychromatic418967fa.accept_11_9_10_1_1_581 42 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 243 (accept_3_5 41 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 243 (Polychromatic418967fa.accept_13_1_11_9_1_1857 40 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 243 (accept_3_5 38 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 243 (accept_3_5 35 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 243 (Polychromatic418967fa.accept_13_8_11_9_1_593 34 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 243 (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 243 (accept_3_5 32 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 243 (accept_3_5 29 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 243 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 243 (accept_3_5 26 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 243
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 243 (accept_3_5 23 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 243 (Polychromatic418967fa.accept_13_8_11_9_1_593 21 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 243 (accept_3_5 20 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 243 (accept_3_5 17 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 243 (Polychromatic418967fa.accept_23_16_7_13_1_14626 16 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 243 (accept_3_5 14 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 243
  (Polychromatic418967fa.accept_17_12_8_5_1_6018 12 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 243 (accept_3_5 11 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 243 (Polychromatic418967fa.accept_16_10_12_3_1_4252 10 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 243 (accept_3_5 8 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 243 (accept_3_5 5 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 76 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 243 (Polychromatic418967fa.accept_17_3_8_5_1_3636 3 76 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 243 (accept_3_5 2 76 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 243 (allA_succ_of_accept
  74 75 243 (Polychromatic418967fa.accept_18_2_3_9_1_1996 74 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 243 (Polychromatic418967fa.accept_18_1_3_9_1_328 73 75 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 243 3 24 25 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 243
  (Polychromatic418967fa.accept_13_6_10_9_1_4329 71 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 243 (Polychromatic418967fa.accept_16_6_11_3_1_2198 70 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 243 3 23 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 68
  75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 67 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 243 3 22 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 65 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 243 (Polychromatic418967fa.accept_13_12_10_9_1_1166 64 75
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 243 3 21 25 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 243
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 62 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 243 (Polychromatic418967fa.accept_18_7_3_9_1_1020 61 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 243 3 20 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 243 (Polychromatic418967fa.accept_19_2_18_15_1_6413
  59 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 243
  (Polychromatic418967fa.accept_10_8_5_3_1_543 58 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 243 3 19 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 243 (Polychromatic418967fa.accept_16_8_11_3_1_4279 56 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 243 (Polychromatic418967fa.accept_16_7_11_3_1_1330 55 75
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 243 3 18 25 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 243
  (Polychromatic418967fa.accept_13_1_10_9_1_215 53 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 52 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 243 3 17 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 243 (Polychromatic418967fa.accept_18_14_3_9_1_4234
  50 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 243
  (Polychromatic418967fa.accept_17_15_7_5_1_9836 49 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 243 3 16 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 47 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 243 (Polychromatic418967fa.accept_16_14_11_3_1_4249 46 75
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 243 3 15 25 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 243
  (Polychromatic418967fa.accept_18_8_3_9_1_4232 44 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 43 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 243 3 14 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 243 (Polychromatic418967fa.accept_19_3_18_15_1_3711
  41 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 243
  (Polychromatic418967fa.accept_13_1_10_9_1_215 40 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 243 3 13 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 38 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 75 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 243 3 12 25 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 243
  (Polychromatic418967fa.accept_19_16_18_15_1_3681 35 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 75 243 (Polychromatic418967fa.accept_22_12_9_1_1_13113 34 75 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 243 3 11 25 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 243
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 243 (Polychromatic418967fa.accept_16_15_11_3_1_2179 31 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 243 3 10 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 243 (Polychromatic418967fa.accept_17_12_7_5_1_8659
  29 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 243
  (Polychromatic418967fa.accept_10_8_5_3_1_543 28 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 75 243 3 9 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 75 243 (Polychromatic418967fa.accept_17_9_7_5_1_1566 26 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 243 (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 75
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 243 3 8 25 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 243
  (Polychromatic418967fa.accept_16_7_11_3_1_1330 23 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 243 3 7 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 243 (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 75 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 243
  (Polychromatic418967fa.accept_13_6_10_9_1_4329 19 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 243 3 6 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 243 (Polychromatic418967fa.accept_19_16_18_15_1_3681 16 75
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 243 3 5 25 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 243
  (Polychromatic418967fa.accept_13_1_10_9_1_215 14 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 243 (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 243 3 4 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 243 (Polychromatic418967fa.accept_17_11_7_5_1_1567 11 75 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 243
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 75 243 3 3 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 75 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 75 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 243 3 2 25 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 243
  (Polychromatic418967fa.accept_20_5_15_3_1_4516 5 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 243 (Polychromatic418967fa.accept_19_4_18_15_1_7899 4 75 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 243 3 1 25 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 75 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 243
  (Polychromatic418967fa.accept_13_1_10_9_1_215 1 75 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 243
  (allA_succ_of_accept 73 74 243 (accept_3_4 73 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  74 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 74 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 243 (accept_3_4 70 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 74 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 243
  (Polychromatic418967fa.accept_20_8_14_3_1_9074 68 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 74 243 (accept_3_4 67 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  74 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 66 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 243 (accept_3_4 64 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 74 243 (Polychromatic418967fa.accept_24_15_2_3_1_14625 63 74 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 62 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 74 243 (accept_3_4 61 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  74 243 (Polychromatic418967fa.accept_16_12_10_3_1_4209 60 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 74 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 243 (accept_3_4 58 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 74 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 243
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 56 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 243 (accept_3_4 55 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 243 (accept_3_4 52 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 74 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 243 (accept_3_4 49 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 243 (accept_3_4 46 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 74 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 243 (accept_3_4 43 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 243 (accept_3_4 40 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 74 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 243
  (Polychromatic418967fa.accept_17_4_6_5_1_9871 38 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 243 (accept_3_4 37 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 243 (accept_3_4 34 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 74 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 243
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 32 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 243 (accept_3_4 31 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 243 (accept_3_4 28 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 74 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 243
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 243 (accept_3_4 25 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 243 (Polychromatic418967fa.accept_18_6_2_9_1_3056 24 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 243 (accept_3_4 22 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 74 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 243 (accept_3_4 19 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 243 (accept_3_4 16 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 74 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 243
  (Polychromatic418967fa.accept_19_14_17_15_1_3761 14 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 74 243 (accept_3_4 13 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 74 243 (Polychromatic418967fa.accept_16_12_10_3_1_4209 12 74 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 74 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 74 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 243 (accept_3_4 10 74 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 74
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 243 (accept_3_4 7 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  243 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 74 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 243 (accept_3_4 4 74 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 243 (Polychromatic418967fa.accept_17_3_6_5_1_8669 3 74 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  74 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 243 (accept_3_4 1 74 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 243 (allA_succ_of_accept
  72 73 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 243 (accept_3_5 71 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 73 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 69 73 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 243 (accept_3_5 68 73 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 243 (Polychromatic418967fa.accept_24_19_1_3_1_9676
  67 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 243 (accept_3_5 65 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 243 (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 73 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 243 (accept_3_5 62 73 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 61 73 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 243
  (Polychromatic418967fa.accept_16_12_9_3_1_5363 60 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 243 (accept_3_5 59 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 243 (accept_3_5 56 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 55 73 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 243 (accept_3_5 53 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 243 (accept_3_5 50 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 243 (Polychromatic418967fa.accept_19_11_16_15_1_11951 49 73 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 243
  (Polychromatic418967fa.accept_20_8_13_3_1_9081 48 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 243 (accept_3_5 47 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 243 (accept_3_5 44 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 73 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 243 (accept_3_5 41 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 243 (accept_3_5 38 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 73 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 243 (accept_3_5 35 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 243 (accept_3_5 32 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 243 (Polychromatic418967fa.accept_15_1_13_3_1_2002 31 73 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 243 (accept_3_5 29 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 243 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 243 (accept_3_5 26 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 73 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 243
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 243 (accept_3_5 23 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 243 (accept_3_5 20 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 243 (Polychromatic418967fa.accept_21_19_10_12_1_5550 19 73 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 243 (accept_3_5 17 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 243 (accept_3_5 14 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 243 (Polychromatic418967fa.accept_19_13_16_15_1_3781 13 73 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 243
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 243 (accept_3_5 11 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 243 (accept_3_5 8 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 73 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 243 (accept_3_5 5 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3 73 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 243 (accept_3_5 2 73 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 243 (allA_succ_of_accept 71
  72 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 71 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 243 (Polychromatic418967fa.accept_20_10_12_3_1_6003 70 72 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 243 3 23 24 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 243
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 68 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 243 3 22 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 65
  72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 243
  (Polychromatic418967fa.accept_21_1_9_12_1_2719 64 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 243 9 7 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 62 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 61 72 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 243 3 20 24 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 243 (Polychromatic418967fa.accept_13_6_7_9_1_1848 58 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 243 3 19 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 243 (Polychromatic418967fa.accept_13_4_7_9_1_5260
  56 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 243
  (Polychromatic418967fa.accept_10_5_2_3_1_239 55 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 243 9 6 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 72 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 243 3 17 24 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 243
  (Polychromatic418967fa.accept_13_11_7_9_1_612 50 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 243 3 16 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 243 (Polychromatic418967fa.accept_13_8_7_9_1_611 47
  72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 46 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 243 9 5 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 243 (Polychromatic418967fa.accept_16_12_8_3_1_4241 44 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 243 (Polychromatic418967fa.accept_13_4_7_9_1_5260 43 72 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 243 3 14 24 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 243
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 243 3 13 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 38
  72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 243
  (Polychromatic418967fa.accept_13_11_7_9_1_612 37 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 243 9 4 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 243 (Polychromatic418967fa.accept_13_8_7_9_1_611 34 72 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 243 3 11 24 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 243 3 10 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182
  29 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 243
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 243 9 3 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 243 (Polychromatic418967fa.accept_21_5_9_12_1_8715 26 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 243 3 8 24 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 243
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 243 (Polychromatic418967fa.accept_15_7_12_3_1_1137 22 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 243 3 7 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 243 (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 72 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 243
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 19 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 243 9 2 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 72 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 243 3 5 24 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 243
  (Polychromatic418967fa.accept_23_14_3_13_1_14624 14 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 72 243 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 72 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 243 3 4 24 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 72 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 72 243 9 1 8 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 72 243 (Polychromatic418967fa.accept_13_8_7_9_1_611 8 72 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 243
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 243 3 2 24 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 72 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 243 3 1 24 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 243
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 2 72 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 72 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 72 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 243 (allA_succ_of_accept 70
  71 243 (accept_3_4 70 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 243 (accept_3_4 67 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 243 (Polychromatic418967fa.accept_22_21_5_1_1_6731
  65 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 243 (accept_3_4 64
  71 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 243
  (Polychromatic418967fa.accept_16_15_7_3_1_4273 63 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 243 (accept_3_4 61 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 71 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 59
  71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 243 (accept_3_4 58 71
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 243
  (Polychromatic418967fa.accept_12_9_11_3_1_772 57 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 243 (accept_3_4 55 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 71 243 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 53
  71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 243 (accept_3_4 52 71
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 243
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 243 (accept_3_4 49 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 71 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 243 (Polychromatic418967fa.accept_16_15_7_3_1_4273
  47 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 243 (accept_3_4 46
  71 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 243 (accept_3_4 43 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 71 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 41
  71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 243 (accept_3_4 40 71
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 243 (accept_3_4 37 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 71 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 243
  (Polychromatic418967fa.accept_21_14_8_12_1_13241 35 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 71 243 (accept_3_4 34 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 71 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 243 (accept_3_4 31 71 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401
  30 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 243
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 29 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 243 (accept_3_4 28 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 243 (accept_3_4 25 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 71 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 243
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 23 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 243 (accept_3_4 22 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 243 (accept_3_4 19 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 71 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 243 (accept_3_4 16 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 243 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 243 (accept_3_4 13 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 71 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 243 (accept_3_4 10 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 243 (accept_3_4 7 71 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 71 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 243
  (Polychromatic418967fa.accept_21_5_8_12_1_7108 5 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 243 (accept_3_4 4 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 71 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 243 (accept_3_4 1 71 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 243
  (allA_succ_of_accept 69 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 70 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 243 (accept_3_5 68 70 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 70 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  66 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 243 (accept_3_5 65
  70 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 243
  (Polychromatic418967fa.accept_19_7_13_15_1_2407 64 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 70 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 70 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 243 (accept_3_5 62 70 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 70 243
  (Polychromatic418967fa.accept_21_18_7_12_1_10175 60 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 70 243 (accept_3_5 59 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 70 243 (Polychromatic418967fa.accept_15_13_10_3_1_1952 58 70 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 70 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 70 243 (accept_3_5 56 70 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 70 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55
  70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 70 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 70 243 (accept_3_5 53 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  70 243 (Polychromatic418967fa.accept_11_8_4_1_1_1000 52 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 70 243 (Polychromatic418967fa.accept_15_6_10_3_1_2844 51 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 70 243 (accept_3_5 50 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 70 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 243
  (Polychromatic418967fa.accept_17_14_2_5_1_3560 48 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 70 243 (accept_3_5 47 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  70 243 (Polychromatic418967fa.accept_21_4_7_12_1_10320 46 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 243 (accept_3_5 44 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 243 (accept_3_5 41 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  70 243 (Polychromatic418967fa.accept_13_1_5_9_1_226 40 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 70 243 (Polychromatic418967fa.accept_15_9_10_3_1_2845 39 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 243 (accept_3_5 38 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 70 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 243
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 70 243 (accept_3_5 35 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  70 243 (Polychromatic418967fa.accept_16_2_6_3_1_5396 34 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 243 (accept_3_5 32 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 243
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 243 (accept_3_5 29 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 243 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 243 (accept_3_5 26 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 243
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 243 (accept_3_5 23 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 243 (Polychromatic418967fa.accept_15_7_10_3_1_2891 22 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 243 (accept_3_5 20 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 243 (accept_3_5 17 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 16 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 243 (accept_3_5 14 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 243
  (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 243 (accept_3_5 11 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 243 (Polychromatic418967fa.accept_23_10_1_13_1_14623 10 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 243 (accept_3_5 8 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 243 (accept_3_5 5 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  243 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 70 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 70 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 243 (accept_3_5 2 70 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 70 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 243 (allA_succ_of_accept 68 69
  243 (Polychromatic418967fa.accept_11_2_3_1_1_244 68 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 69 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 69 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 243 3 22 23 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 65 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 64 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 243 3 21 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 62
  69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 61 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 243 3 20 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 59 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 69 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 243 3 19 23 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 243
  (Polychromatic418967fa.accept_10_6_9_3_1_935 56 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 55 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 243 3 18 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 53
  69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 243
  (Polychromatic418967fa.accept_18_16_15_9_1_6852 52 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 243 3 17 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 69 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 243 3 16 23 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 47 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 243 3 15 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907
  44 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 43 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 243 3 14 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 243 (Polychromatic418967fa.accept_15_10_9_3_1_1947 40 69
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 243 3 13 23 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 243 3 12 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 35
  69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 243 3 11 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 69 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 243 3 10 23 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 243 (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 243 3 9 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 69 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 243 3 8 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 69 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 243 3 7 23 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 243
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 20 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 243 3 6 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 69 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 243
  (Polychromatic418967fa.accept_10_6_9_3_1_935 16 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 243 3 5 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 69 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 243 3 4 23 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 243 3 3 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 69 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 243 3 2 23 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 69 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 243 3 1 23 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 69 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 69 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 243 (allA_succ_of_accept 67 68 243 (accept_3_4 67 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 68 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 66 68 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 243 (accept_3_4 64 68 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 63
  68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 243
  (Polychromatic418967fa.accept_19_5_11_15_1_2460 62 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 243 (accept_3_4 61 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 243 (Polychromatic418967fa.accept_13_8_3_9_1_5269 60 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 243 (accept_3_4 58 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 243 (Polychromatic418967fa.accept_13_5_3_9_1_1189 57 68 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 243 (accept_3_4 55 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 54 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 243 (accept_3_4 52 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 68 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 243
  (Polychromatic418967fa.accept_15_5_8_3_1_556 50 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 243 (accept_3_4 49 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 243 (Polychromatic418967fa.accept_19_10_11_15_1_3699 48 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 243 (accept_3_4 46 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 68 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 243
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 44 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 243 (accept_3_4 43 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 243 (accept_3_4 40 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 68 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 243
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 38 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 243 (accept_3_4 37 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 243 (accept_3_4 34 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 243 (Polychromatic418967fa.accept_13_7_3_9_1_1142 33 68 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 243
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 243 (accept_3_4 31 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 243 (accept_3_4 28 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 68 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 243 (accept_3_4 25 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 243 (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 243 (accept_3_4 22 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 68 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 243
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 20 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 243 (accept_3_4 19 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 243 (accept_3_4 16 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 68 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 243
  (Polychromatic418967fa.accept_11_3_2_1_1_994 14 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 243 (accept_3_4 13 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 243 (accept_3_4 10 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 243 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 68 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 243
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 8 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 243 (accept_3_4 7 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  243 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 243 (accept_3_4 4 68 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 68 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 243 (Polychromatic418967fa.accept_13_2_3_9_1_2610 2
  68 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 243 (accept_3_4 1 68 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 243 (allA_succ_of_accept 66 67
  243 (Polychromatic418967fa.accept_10_6_7_3_1_547 66 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 67 243 (accept_3_5 65 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 67 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 243 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 67
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 243 (accept_3_5 62 67 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 243
  (Polychromatic418967fa.accept_19_4_10_15_1_9243 61 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 67 243 (Polychromatic418967fa.accept_18_6_13_9_1_4218 60 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 67 243 (accept_3_5 59 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 67 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 67 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 67 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 57
  67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 243 (accept_3_5 56 67
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 55 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 67 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 67 243 (accept_3_5 53 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 67 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 67 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 51
  67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 243 (accept_3_5 50 67
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 243
  (Polychromatic418967fa.accept_15_4_7_3_1_119 49 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 67 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 67 243 (accept_3_5 47 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 67 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 67 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 243 (Polychromatic418967fa.accept_10_5_7_3_1_561
  45 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 243 (accept_3_5 44
  67 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 43 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 67 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 42 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 243 (accept_3_5 41 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 67 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 243 (Polychromatic418967fa.accept_18_3_13_9_1_4260
  39 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 243 (accept_3_5 38
  67 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 67 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 243 (accept_3_5 35 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 67 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 67 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  33 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 243 (accept_3_5 32
  67 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 243
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 67 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 243 (accept_3_5 29 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 67 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 27
  67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 243 (accept_3_5 26 67
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 25 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 67 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 243 (accept_3_5 23 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 67 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 67 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  21 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 243 (accept_3_5 20
  67 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 243
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 67 243 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 243 (accept_3_5 17 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 67 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 243 (accept_3_5 14 67
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 67 243 (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 243 (accept_3_5 11 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 67 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 67 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9
  67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 243 (accept_3_5 8 67 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 243 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7
  67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 243 (accept_3_5 5 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 243 (accept_3_5 2 67 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 67 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 243 (allA_succ_of_accept 65 66
  243 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 243 3 21 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 62
  66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 243 3 20 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 59 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 66 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 243 3 19 22 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 56 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 243 (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 243 3 18 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 66
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 52 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 243 3 17 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 66 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 243 3 16 22 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 243
  (Polychromatic418967fa.accept_10_7_6_3_1_927 47 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 46 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 243 3 15 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 44
  66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 243 3 14 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 66 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 243 3 13 22 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 243 3 12 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 35
  66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 34 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 243 3 11 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 243 (Polychromatic418967fa.accept_13_5_1_9_1_618 31 66 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 243 3 10 22 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 243 3 9 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 66 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 243 3 8 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 66 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 243 3 7 22 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 243 3 6 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 66 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 243 3 5 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 66 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 243 3 4 22 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 243
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 243 3 3 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 66 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 243
  (Polychromatic418967fa.accept_10_7_6_3_1_927 7 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 243 3 2 22 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 66 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 243 3 1 22 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 66 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 66 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 243 (allA_succ_of_accept 64 65 243 (accept_3_4 64 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 243 (Polychromatic418967fa.accept_14_7_9_5_1_529 63 65 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 65 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 243 (accept_3_4 61 65 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 60
  65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 243 (accept_3_4 58 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 243 (accept_3_4 55 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 65 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 243 (accept_3_4 52 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 51 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 243 (accept_3_4 49 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 65 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 243 (accept_3_4 46 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 243 (accept_3_4 43 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 65 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 243
  (Polychromatic418967fa.accept_19_3_8_15_1_2523 41 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 243 (accept_3_4 40 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 243 (accept_3_4 37 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 65 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 243
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 243 (accept_3_4 34 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 243 (accept_3_4 31 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 65 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 243
  (Polychromatic418967fa.accept_16_13_1_3_1_2205 29 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 243 (accept_3_4 28 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 243 (accept_3_4 25 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 65 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 243
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 243 (accept_3_4 22 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 243 (accept_3_4 19 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 65 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 243 (accept_3_4 16 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 243 (Polychromatic418967fa.accept_18_15_11_9_1_4256 15 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 243 (accept_3_4 13 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 65 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 243 (accept_3_4 10 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 243 (accept_3_4 7 65 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 65 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 243
  (Polychromatic418967fa.accept_22_5_21_1_1_11610 5 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 243 (accept_3_4 4 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 65 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 65 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 243 (accept_3_4 1 65 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 243
  (allA_succ_of_accept 63 64 243 (Polychromatic418967fa.accept_22_19_20_1_1_6783 63 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 243 (accept_3_5 62 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 60
  64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 243 (accept_3_5 59 64
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 243
  (Polychromatic418967fa.accept_22_14_20_1_1_6722 58 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 64 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 243 (accept_3_5 56 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186
  54 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 243 (accept_3_5 53
  64 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 52 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 64 243 (Polychromatic418967fa.accept_18_15_10_9_1_2009 51 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 243 (accept_3_5 50 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 48
  64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 243 (accept_3_5 47 64
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 46 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 64 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 243 (accept_3_5 44 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 243 (Polychromatic418967fa.accept_12_6_4_3_1_361
  42 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 243 (accept_3_5 41
  64 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 243
  (Polychromatic418967fa.accept_21_19_1_12_1_5485 40 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 64 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 243 (accept_3_5 38 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 243
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 64 243 (accept_3_5 35 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  64 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 64 243 (Polychromatic418967fa.accept_18_15_10_9_1_2009 33 64 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 243 (accept_3_5 32 64 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 64 243 (accept_3_5 29 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  64 243 (Polychromatic418967fa.accept_21_7_1_12_1_13236 28 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 64 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 64 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 243 (accept_3_5 26 64 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 64 243 (accept_3_5 23 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  64 243 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 64 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 64 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 243 (accept_3_5 20 64 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 64 243 (accept_3_5 17 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  64 243 (Polychromatic418967fa.accept_13_3_12_9_1_1193 16 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 64 243 (Polychromatic418967fa.accept_17_15_13_5_1_9877 15 64 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 243 (accept_3_5 14 64 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 243
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 243 (accept_3_5 11 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 64 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 243 (accept_3_5 8 64 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 243 (accept_3_5 5 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  243 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 64 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 243 (accept_3_5 2 64 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 243 (allA_succ_of_accept 62 63 243
  (Polychromatic418967fa.accept_19_5_6_15_1_10686 62 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 243 (Polychromatic418967fa.accept_16_13_15_3_1_4196 61 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 243 3 20 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  59 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 243
  (Polychromatic418967fa.accept_14_2_7_5_1_5450 58 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 243 3 19 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 63 243 (Polychromatic418967fa.accept_22_12_19_1_1_14601 56 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 243 (Polychromatic418967fa.accept_16_7_15_3_1_1302 55 63
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 243 9 6 7 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 243
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 53 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 243 3 17 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 243 (Polychromatic418967fa.accept_16_2_15_3_1_1300
  50 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 243
  (Polychromatic418967fa.accept_19_11_6_15_1_14622 49 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 63 243 3 16 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 63 243 (Polychromatic418967fa.accept_13_8_11_9_1_593 47 63 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 243
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 46 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 63 243 9 5 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 44 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 243 (Polychromatic418967fa.accept_16_11_15_3_1_1304 43 63
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 243 3 14 21 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 243
  (Polychromatic418967fa.accept_13_2_11_9_1_591 41 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 243 (Polychromatic418967fa.accept_13_1_11_9_1_1857 40 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 243 3 13 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 243
  (Polychromatic418967fa.accept_22_16_19_1_1_14621 38 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 63 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 63 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 63 243 9 4 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 63 243 (Polychromatic418967fa.accept_19_16_6_15_1_2441
  35 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 243
  (Polychromatic418967fa.accept_13_8_11_9_1_593 34 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 63 243 3 11 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 63 243 (Polychromatic418967fa.accept_19_13_6_15_1_9287 32 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 243 (Polychromatic418967fa.accept_19_12_6_15_1_5064 31 63
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 243 3 10 21 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 243
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 29 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 63 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 63 243 9 3 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 63 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 243
  (Polychromatic418967fa.accept_17_8_12_5_1_1577 25 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 63 243 3 8 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 63 243 (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 243 (Polychromatic418967fa.accept_24_22_15_3_1_13008 22 63
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 243 3 7 21 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 20 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 243 (Polychromatic418967fa.accept_23_19_17_13_1_14620 19 63 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 243 9 2 7 27 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 243
  (Polychromatic418967fa.accept_25_17_13_18_1_7427 17 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 63 243 (Polychromatic418967fa.accept_14_2_7_5_1_5450 16 63 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 243 3 5 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 243 (Polychromatic418967fa.accept_13_1_11_9_1_1857
  14 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 63 243
  (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 63 243 3 4 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 63 243 (Polychromatic418967fa.accept_16_11_15_3_1_1304 11 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 243 (Polychromatic418967fa.accept_17_10_12_5_1_6028 10 63
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 63 243 9 1 7 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 63 243
  (Polychromatic418967fa.accept_13_8_11_9_1_593 8 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 243 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 243 3 2 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 243 (Polychromatic418967fa.accept_19_5_6_15_1_10686 5 63 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 63 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 243 3 1 21 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 243 (Polychromatic418967fa.accept_13_2_11_9_1_591 2 63 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 243 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 63 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 243 (allA_succ_of_accept 61 62 243
  (accept_3_4 61 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 60 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 62 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 243 (accept_3_4 58 62 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 243
  (Polychromatic418967fa.accept_25_6_12_18_1_9362 56 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 62 243 (accept_3_4 55 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  62 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 62 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 243 (accept_3_4 52 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 62 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 62 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 243 (accept_3_4 49 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 243 (Polychromatic418967fa.accept_19_10_5_15_1_6443 48 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 243 (accept_3_4 46 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 62 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 243
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 44 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 243 (accept_3_4 43 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 243 (accept_3_4 40 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 62 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 243
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 38 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 243 (accept_3_4 37 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 243 (accept_3_4 34 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 62 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 243 (accept_3_4 31 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 243 (accept_3_4 28 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 243 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 62 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 243
  (Polychromatic418967fa.accept_23_3_16_13_1_14619 26 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 62 243 (accept_3_4 25 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 62 243 (Polychromatic418967fa.accept_17_7_11_5_1_3539 24 62 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 62 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 243 (accept_3_4 22 62 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 243
  (Polychromatic418967fa.accept_15_5_2_3_1_4876 20 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 243 (accept_3_4 19 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 243 (accept_3_4 16 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 62 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 243
  (Polychromatic418967fa.accept_13_1_10_9_1_215 14 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 243 (accept_3_4 13 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 243 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 243 (accept_3_4 10 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 62 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 243 (accept_3_4 7 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  243 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 62 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 243 (accept_3_4 4 62 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 243 (Polychromatic418967fa.accept_18_3_8_9_1_1956 3 62 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 243 (Polychromatic418967fa.accept_22_2_18_1_1_13081
  2 62 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 243 (accept_3_4 1 62
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 243 (allA_succ_of_accept 60 61 243
  (Polychromatic418967fa.accept_11_5_6_1_1_988 60 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 243 (accept_3_5 59 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 243 (accept_3_5 56 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 243 (Polychromatic418967fa.accept_25_5_11_18_1_14618 55 61 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 243 (accept_3_5 53 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 243 (accept_3_5 50 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 61 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 243
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 243 (accept_3_5 47 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 45 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 243 (accept_3_5 44 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 243 (Polychromatic418967fa.accept_15_13_1_3_1_1972 43 61 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 243 (accept_3_5 41 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 243 (Polychromatic418967fa.accept_18_3_7_9_1_5486 39 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 243 (accept_3_5 38 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 243 (Polychromatic418967fa.accept_19_18_4_15_1_3721 37 61 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 243
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 243 (accept_3_5 35 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 243 (accept_3_5 32 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 243 (Polychromatic418967fa.accept_16_15_13_3_1_4215 31 61 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 243 (accept_3_5 29 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 243 (accept_3_5 26 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 243 (Polychromatic418967fa.accept_19_6_4_15_1_2432 25 61 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 243
  (Polychromatic418967fa.accept_16_8_13_3_1_4253 24 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 243 (accept_3_5 23 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 243 (accept_3_5 20 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 243 (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 61 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 243 (accept_3_5 17 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 243 (Polychromatic418967fa.accept_16_15_13_3_1_4215 15 61 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 243 (accept_3_5 14 61 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 243 (Polychromatic418967fa.accept_15_13_1_3_1_1972 13 61
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 243
  (Polychromatic418967fa.accept_10_2_1_3_1_233 12 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 243 (accept_3_5 11 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 243 (accept_3_5 8 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 61 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 243 (accept_3_5 5 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 243 (Polychromatic418967fa.accept_18_3_7_9_1_5486 3 61 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 243 (accept_3_5 2 61 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 243 (Polychromatic418967fa.accept_16_1_13_3_1_2168 1 61 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 243 (allA_succ_of_accept 59 60 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 59 60 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 58 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 243 3 19 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 243 (Polychromatic418967fa.accept_13_4_8_9_1_1156 56 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 60 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 243 3 18 20 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 243
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 53 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 243 (Polychromatic418967fa.accept_16_4_12_3_1_2180 52 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 243 3 17 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 50
  60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 243
  (Polychromatic418967fa.accept_18_13_6_9_1_4280 49 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 243 3 16 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 243 (Polychromatic418967fa.accept_13_7_8_9_1_1158 46 60 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 243 3 15 20 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 243 3 14 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 41
  60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 243
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 40 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 60 243 3 13 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 38 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 60 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 243 3 12 20 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 243
  (Polychromatic418967fa.accept_19_16_3_15_1_14603 35 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 60 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 60 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 243 3 11 20 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 243
  (Polychromatic418967fa.accept_18_14_6_9_1_1950 32 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 60 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 243 3 10 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 243
  (Polychromatic418967fa.accept_11_6_5_1_1_586 28 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 60 243 3 9 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 60 243 (Polychromatic418967fa.accept_16_10_12_3_1_4252 26 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 60
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 243 3 8 20 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 243 3 7 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 60 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 60 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 243
  (Polychromatic418967fa.accept_18_1_6_9_1_2001 19 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 243 3 6 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 60 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 243 3 5 20 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 243
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 60 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 243 3 4 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 243 (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 60 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 243
  (Polychromatic418967fa.accept_16_10_12_3_1_4252 10 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 60 243 3 3 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 60 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 60 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 243 3 2 20 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 243
  (Polychromatic418967fa.accept_21_5_18_12_1_5531 5 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 243 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 60 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 243 3 1 20 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 60 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 243)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 243 (allA_succ_of_accept 58
  59 243 (accept_3_4 58 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 243 (accept_3_4 55 59 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 243
  (Polychromatic418967fa.accept_22_9_15_1_1_13101 53 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 243 (accept_3_4 52 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 243 (accept_3_4 49 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 243 (Polychromatic418967fa.accept_18_12_5_9_1_6896 48 59 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 243
  (Polychromatic418967fa.accept_13_8_7_9_1_611 47 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 243 (accept_3_4 46 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 243 (accept_3_4 43 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 42 59 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 243
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 243 (accept_3_4 40 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 243 (Polychromatic418967fa.accept_16_7_11_3_1_1330 39 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 243 (accept_3_4 37 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 59 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 243
  (Polychromatic418967fa.accept_25_10_9_18_1_14617 35 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 59 243 (accept_3_4 34 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 59 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 59 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 243 (accept_3_4 31 59 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 30
  59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 243 (accept_3_4 28 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 243 (Polychromatic418967fa.accept_19_8_2_15_1_2426 27 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 243 (accept_3_4 25 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 59 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 243 (accept_3_4 22 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 243 (accept_3_4 19 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 243 (Polychromatic418967fa.accept_19_18_2_15_1_3718 18 59 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 243
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 17 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 243 (accept_3_4 16 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 243 (accept_3_4 13 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 243 (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 59 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 243
  (Polychromatic418967fa.accept_13_11_7_9_1_612 11 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 243 (accept_3_4 10 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 243 (accept_3_4 7 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 59 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 243
  (Polychromatic418967fa.accept_21_5_17_12_1_14616 5 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 243 (accept_3_4 4 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 59 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 243 (accept_3_4 1 59 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 243
  (allA_succ_of_accept 57 58 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 243 (accept_3_5 56 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  54 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 243 (accept_3_5 53
  58 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 52 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 243 (accept_3_5 50 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 243 (Polychromatic418967fa.accept_18_12_4_9_1_5452
  48 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 243 (accept_3_5 47
  58 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 46 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 58 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 243 (accept_3_5 44 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 58 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  42 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 243 (accept_3_5 41
  58 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 243
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 58 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 243 (accept_3_5 38 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 58 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 243 (Polychromatic418967fa.accept_10_6_8_3_1_930
  36 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 243 (accept_3_5 35
  58 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 243
  (Polychromatic418967fa.accept_25_9_8_18_1_14615 34 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 58 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 243 (accept_3_5 32 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 58 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  30 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 243 (accept_3_5 29
  58 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 243
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 28 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 58 243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 243 (accept_3_5 26 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 58 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 24
  58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 243 (accept_3_5 23 58
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 243
  (Polychromatic418967fa.accept_20_2_18_3_1_4519 22 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 58 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 243 (accept_3_5 20 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 58 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 18
  58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 243 (accept_3_5 17 58
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 16 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 58 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 243 (accept_3_5 14 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 58 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 243
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 243 (accept_3_5 11 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 243 (accept_3_5 8 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 58 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 243 (accept_3_5 5 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  243 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 58 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 243 (accept_3_5 2 58 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 58 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 243 (allA_succ_of_accept 56 57 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 56 57 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 55 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 57 243 3 18 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 57 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 57 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 243 3 17 19 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 243 3 16 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 47
  57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 57 243 3 15 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 57 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 44 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 57
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 243 3 14 19 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 243 (Polychromatic418967fa.accept_13_1_5_9_1_226 40 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 243 3 13 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 57 243 3 12 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 57 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 57 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 243 3 11 19 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 243 3 10 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 29
  57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 243
  (Polychromatic418967fa.accept_13_2_5_9_1_610 28 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 57 243 3 9 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 57 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 57 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 243 3 8 19 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 23 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 243 3 7 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 57 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 57 243 3 6 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 57 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 57 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 243 3 5 19 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 243 3 4 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 57 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 57 243 3 3 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 57 243 (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 57 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 243 3 2 19 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 57 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 243 3 1 19 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 57 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 57 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 243))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 243 (allA_succ_of_accept 55 56
  243 (accept_3_4 55 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 56 243
  (Polychromatic418967fa.accept_12_6_8_3_1_82 54 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 56 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 243 (accept_3_4 52 56 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 56 243 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 56 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 243
  (Polychromatic418967fa.accept_19_12_18_15_1_10690 50 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 56 243 (accept_3_4 49 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 56 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 56 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 56 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 243 (accept_3_4 46 56 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 243 (Polychromatic418967fa.accept_13_6_4_9_1_4326
  45 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 243
  (Polychromatic418967fa.accept_13_5_4_9_1_601 44 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 243 (accept_3_4 43 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 243 (accept_3_4 40 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 56 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 243 (accept_3_4 37 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 243 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 243 (accept_3_4 34 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 243 (Polychromatic418967fa.accept_13_7_4_9_1_1865 33 56 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 243
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 32 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 243 (accept_3_4 31 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 243 (accept_3_4 28 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 243 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 56 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 243
  (Polychromatic418967fa.accept_19_7_18_15_1_5061 26 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 243 (accept_3_4 25 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 243 (Polychromatic418967fa.accept_18_6_2_9_1_3056 24 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 243 (accept_3_4 22 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 243 (Polychromatic418967fa.accept_13_8_4_9_1_1145 21 56 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 243
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 20 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 243 (accept_3_4 19 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 243 (accept_3_4 16 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 243 (Polychromatic418967fa.accept_21_15_14_12_1_8736 15 56 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 243
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 243 (accept_3_4 13 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 243 (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 243 (accept_3_4 10 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 56 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 243 (accept_3_4 7 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  243 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 243 (accept_3_4 4 56 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 243 (Polychromatic418967fa.accept_18_3_2_9_1_1013 3 56 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 243 (Polychromatic418967fa.accept_19_2_18_15_1_6413
  2 56 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 243 (accept_3_4 1 56
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 243))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 243 (allA_succ_of_accept 54 55 243 (Polychromatic418967fa.accept_13_2_3_9_1_2610 54 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 243 (accept_3_5 53 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 243
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 51 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 243 (accept_3_5 50 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 243 (Polychromatic418967fa.accept_20_9_15_3_1_7470 49 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 243 (accept_3_5 47 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 243 (accept_3_5 44 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 243 (accept_3_5 41 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 243 (accept_3_5 38 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 243 (accept_3_5 35 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 243 (accept_3_5 32 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 243 (Polychromatic418967fa.accept_13_5_3_9_1_1189 31 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 243 (Polychromatic418967fa.accept_20_10_15_3_1_7387 30 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 243 (accept_3_5 29 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 243 (accept_3_5 26 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 243 (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 243 (accept_3_5 23 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 55 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 243 (accept_3_5 20 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 243 (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 243 (accept_3_5 17 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 243 (accept_3_5 14 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 243 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 243 (accept_3_5 11 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 55 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 243 (accept_3_5 8 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  243 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 243 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 55 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 243 (accept_3_5 5 55 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 243 (Polychromatic418967fa.accept_18_3_1_9_1_1929 3
  55 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 243 (accept_3_5 2 55 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 55
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 243 (allA_succ_of_accept 53 54 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 243 3 17 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 50
  54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 243 3 16 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 47 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 46 54
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 243 9 5 6 27 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 44 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 243 (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 243 3 14 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 54
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 54 243 3 13 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 54 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 38 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 54 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 243 9 4 6 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 243
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 243 3 11 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 32
  54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 243
  (Polychromatic418967fa.accept_11_9_10_1_1_581 31 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 243 3 10 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 54 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 243 27 1 2 9 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 26 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 243 3 8 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 243 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 54 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 54 243 3 7 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 54 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 54 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 243 9 2 6 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 243 3 5 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 54 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 243 3 4 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 243 (Polychromatic418967fa.accept_13_11_2_9_1_2640 11 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 54 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 243 9 1 6 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 243 3 2 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 54 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 54 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 54 243 3 1 18 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 54 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 54 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 54 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  243)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 243 (allA_succ_of_accept 52 53 243 (accept_3_4
  52 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 243 (accept_3_4 49 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 53 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 243 (Polychromatic418967fa.accept_13_8_1_9_1_1178
  47 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 243 (accept_3_4 46
  53 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 243
  (Polychromatic418967fa.accept_12_9_5_3_1_782 45 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 243 (accept_3_4 43 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 53 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 41
  53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 243 (accept_3_4 40 53
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 243
  (Polychromatic418967fa.accept_15_9_8_3_1_557 39 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 243 (accept_3_4 37 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 53 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 243 (Polychromatic418967fa.accept_15_5_8_3_1_556
  35 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 243 (accept_3_4 34
  53 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 243
  (Polychromatic418967fa.accept_12_9_5_3_1_782 33 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 53 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 243 (accept_3_4 31 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 53 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 53 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 243 (accept_3_4 28 53
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 53 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 243 (accept_3_4 25 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 53 243 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 53 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 243 (accept_3_4 22 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 243 (accept_3_4 19 53 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 53 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 243
  (Polychromatic418967fa.accept_23_17_7_13_1_13032 17 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 53 243 (accept_3_4 16 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 53 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 53 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 53 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 243 (accept_3_4 13 53 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995
  12 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 243
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 11 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 243 (accept_3_4 10 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 243 (accept_3_4 7 53 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 53 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 243
  (Polychromatic418967fa.accept_13_5_1_9_1_618 5 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 243 (accept_3_4 4 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  243 (Polychromatic418967fa.accept_17_3_2_5_1_2556 3 53 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 53 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 53 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 243 (accept_3_4 1 53 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 53 243))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 243
  (allA_succ_of_accept 51 52 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 52 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 243 (accept_3_5 50 52 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047
  48 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 52 243 (accept_3_5 47
  52 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 52 243
  (Polychromatic418967fa.accept_25_21_2_18_1_14614 46 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 243 (accept_3_5 44 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 243 (accept_3_5 41 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 243 (Polychromatic418967fa.accept_14_12_10_5_1_2712 40 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 243 (accept_3_5 38 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 243 (accept_3_5 35 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 243 (Polychromatic418967fa.accept_15_4_7_3_1_119 34 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 243 (Polychromatic418967fa.accept_16_1_4_3_1_3148 33 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 243 (accept_3_5 32 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 243 (accept_3_5 29 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 243 (Polychromatic418967fa.accept_16_12_4_3_1_4295 28 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 243 (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 52 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 243 (accept_3_5 26 52 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 243
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 24 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 243 (accept_3_5 23 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 243 (accept_3_5 20 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 243 (accept_3_5 17 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 243 (accept_3_5 14 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 243
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 243 (accept_3_5 11 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 243 (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 243 (accept_3_5 8 52 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 243
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 243 (accept_3_5 5 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 52 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 52 243 (Polychromatic418967fa.accept_21_3_10_12_1_10278 3 52 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 243 (accept_3_5 2 52 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 52 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52
  243)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 243 (allA_succ_of_accept 50 51 243
  (Polychromatic418967fa.accept_11_6_7_1_1_564 50 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 243 (Polychromatic418967fa.accept_13_10_12_9_1_1837 49 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 243 3 16 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 243 (Polychromatic418967fa.accept_13_8_12_9_1_1168
  47 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 46 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 243 3 15 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 243 (Polychromatic418967fa.accept_19_6_13_15_1_2406 44 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 243 (Polychromatic418967fa.accept_21_1_9_12_1_2719 43 51
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 243 3 14 17 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 243
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 243 (Polychromatic418967fa.accept_15_10_6_3_1_1160 40 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 243 3 13 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 38
  51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 243
  (Polychromatic418967fa.accept_21_16_9_12_1_8697 37 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 243 3 12 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 243 (Polychromatic418967fa.accept_14_7_9_5_1_529 35 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 243 (Polychromatic418967fa.accept_13_8_12_9_1_1168 34 51
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 243 3 11 17 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 243 3 10 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 243 (Polychromatic418967fa.accept_13_3_12_9_1_1193
  29 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 243
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 243 3 9 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 243 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 51 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 243 3 8 17 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 243
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 23 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 22 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 243 3 7 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 20 51 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 243
  (Polychromatic418967fa.accept_21_19_9_12_1_4071 19 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 243 3 6 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 243 (Polychromatic418967fa.accept_13_3_12_9_1_1193 16 51
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 243 3 5 17 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 243
  (Polychromatic418967fa.accept_19_14_13_15_1_2532 14 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 51 243 (Polychromatic418967fa.accept_20_13_11_3_1_4509 13 51 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 243 3 4 17 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 243 3 3 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 51 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 243
  (Polychromatic418967fa.accept_14_7_9_5_1_529 7 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 51 243 3 2 17 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 51 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 51 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 243 3 1 17 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 243
  (Polychromatic418967fa.accept_10_2_1_3_1_233 2 51 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 51 243 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 51 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 51 243))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 243
  (allA_succ_of_accept 49 50 243 (accept_3_4 49 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  50 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 50 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 243 (accept_3_4 46 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 50 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 50 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 243
  (Polychromatic418967fa.accept_19_6_12_15_1_7895 44 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 243 (accept_3_4 43 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 243 (accept_3_4 40 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 50 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 243 (accept_3_4 37 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 243 (accept_3_4 34 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 50 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 243 (accept_3_4 31 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 243 (accept_3_4 28 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 50 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 243
  (Polychromatic418967fa.accept_19_7_12_15_1_13329 26 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 50 243 (accept_3_4 25 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 50 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 50 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 50 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 50 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 243 (accept_3_4 22 50 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 243 (accept_3_4 19 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 243 (accept_3_4 16 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 243 (Polychromatic418967fa.accept_13_2_11_9_1_591 15 50 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 243
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 14 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 243 (accept_3_4 13 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 243 (Polychromatic418967fa.accept_20_12_10_3_1_4537 12 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 243 (accept_3_4 10 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 50 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 243
  (Polychromatic418967fa.accept_13_8_11_9_1_593 8 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 243 (accept_3_4 7 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  243 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 50 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 243 (accept_3_4 4 50 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 50 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 243 (Polychromatic418967fa.accept_13_2_11_9_1_591 2
  50 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 243 (accept_3_4 1 50 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 243)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 243 (allA_succ_of_accept 48 49 243 (Polychromatic418967fa.accept_19_10_11_15_1_3699 48 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 243 (accept_3_5 47 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 49 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 243 (accept_3_5 44 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 243 (Polychromatic418967fa.accept_19_5_11_15_1_2460 43 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 243 (accept_3_5 41 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 243
  (Polychromatic418967fa.accept_11_6_5_1_1_586 39 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 243 (accept_3_5 38 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 243 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 243 (accept_3_5 35 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 49 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 243 (accept_3_5 32 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 243 (Polychromatic418967fa.accept_15_1_4_3_1_1928 31 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 243 (accept_3_5 29 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 243
  (Polychromatic418967fa.accept_13_1_10_9_1_215 27 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 243 (accept_3_5 26 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 243 (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 243 (accept_3_5 23 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 49 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 243 (accept_3_5 20 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 243 (Polychromatic418967fa.accept_13_6_10_9_1_4329 19 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 243 (accept_3_5 17 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 243
  (Polychromatic418967fa.accept_20_15_9_3_1_7435 15 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 243 (accept_3_5 14 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 243 (Polychromatic418967fa.accept_16_13_1_3_1_2205 13 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 243 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 49 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 243 (accept_3_5 11 49 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 49 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 243 (accept_3_5 8 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  243 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 49 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 243 (accept_3_5 5 49 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 49 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 243
  (Polychromatic418967fa.accept_18_3_13_9_1_4260 3 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 49 243 (accept_3_5 2 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49
  243 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 49 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 49 243))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 243 (allA_succ_of_accept
  47 48 243 (Polychromatic418967fa.accept_18_11_12_9_1_992 47 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 48 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 48 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 243 3 15 16 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 243
  (Polychromatic418967fa.accept_17_10_14_5_1_11167 44 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 243 3 14 16 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 243
  (Polychromatic418967fa.accept_10_1_8_3_1_947 41 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 48 243 (Polychromatic418967fa.accept_18_4_12_9_1_2011 40 48 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 48 243 3 13 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 48 243 (Polychromatic418967fa.accept_20_18_8_3_1_9071
  38 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 243
  (Polychromatic418967fa.accept_21_16_6_12_1_2706 37 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 243 3 12 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 48 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 243 (Polychromatic418967fa.accept_18_16_12_9_1_5504 34 48
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 243 3 11 16 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 48 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 48 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 243 3 10 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 29
  48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 243
  (Polychromatic418967fa.accept_18_10_12_9_1_2012 28 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 48 243 3 9 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 48 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 48 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 48 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 243 3 8 16 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 243
  (Polychromatic418967fa.accept_18_5_12_9_1_6871 23 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 48 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 243 3 7 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 243 (Polychromatic418967fa.accept_25_20_23_18_1_14613 20 48
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 243
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 243 3 6 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 243 (Polychromatic418967fa.accept_18_17_12_9_1_3031 17 48 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 48 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 243 3 5 16 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 243
  (Polychromatic418967fa.accept_19_14_10_15_1_13366 14 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 48 243 (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 48 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 243 3 4 16 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 48 243 (Polychromatic418967fa.accept_17_10_14_5_1_11167 10 48 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 243 3 3 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 48 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 243
  (Polychromatic418967fa.accept_21_7_6_12_1_10316 7 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 243 3 2 16 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 243 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 48 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 48 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 243 3 1 16 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 243
  (Polychromatic418967fa.accept_17_2_14_5_1_2575 2 48 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 48 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 48 243)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 243
  (allA_succ_of_accept 46 47 243 (accept_3_4 46 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 243 (accept_3_4 43 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 42 47 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 243
  (Polychromatic418967fa.accept_19_3_9_15_1_9240 41 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 243 (accept_3_4 40 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 243 (Polychromatic418967fa.accept_16_7_15_3_1_1302 39 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 243 (accept_3_4 37 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 47 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 243 (accept_3_4 34 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 243 (accept_3_4 31 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 243 (Polychromatic418967fa.accept_13_4_8_9_1_1156 30 47 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 243
  (Polychromatic418967fa.accept_13_3_8_9_1_1134 29 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 243 (accept_3_4 28 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 243 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 243 (accept_3_4 25 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 47 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 243
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 23 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 243 (accept_3_4 22 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 243 (accept_3_4 19 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 243 (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 47 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 243
  (Polychromatic418967fa.accept_13_4_8_9_1_1156 17 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 243 (accept_3_4 16 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 243 (accept_3_4 13 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 47 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 243
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 11 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 243 (accept_3_4 10 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 243 (accept_3_4 7 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 47 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 243 (accept_3_4 4 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3 47 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 243 (accept_3_4 1 47 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 243))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 243
  (allA_succ_of_accept 45 46 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 243 (accept_3_5 44 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 46 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 46 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  42 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 243 (accept_3_5 41
  46 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 243
  (Polychromatic418967fa.accept_19_2_8_15_1_2447 40 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 243 (accept_3_5 38 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 46 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 36
  46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 243 (accept_3_5 35 46
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 46 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 243 (accept_3_5 32 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 46 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 46 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 30
  46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 243 (accept_3_5 29 46
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 243 (accept_3_5 26 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 46 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 243 (Polychromatic418967fa.accept_13_11_7_9_1_612
  24 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 243 (accept_3_5 23
  46 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 22 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 243 (accept_3_5 20 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 46 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  18 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 243 (accept_3_5 17
  46 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 46 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 243 (accept_3_5 14 46 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 46 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 46 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 243
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 46 243 (accept_3_5 11 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  46 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 46 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 46 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 243 (accept_3_5 8 46 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 46 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 46 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 46 243 (accept_3_5 5 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46
  243 (Polychromatic418967fa.accept_13_4_7_9_1_5260 4 46 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 46 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 46 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 243 (accept_3_5 2 46 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 46 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46 243))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 45 243 (allA_succ_of_accept 44 45 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 45 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 43 45 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 45 243 3 14 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 45 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 45 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 45 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 45 243 3 13 15 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 45 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 45 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 243 9 4 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 45 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 45 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 45 243 3 11 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 45 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 45 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 45 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 243 3 10 15 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 45 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 45 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 243 9 3 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 45 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 45 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 45 243 3 8 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 45 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 45 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 45 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 243 3 7 15 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 243
  (Polychromatic418967fa.accept_13_7_6_9_1_1831 20 45 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 45 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 243 9 2 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 45 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 45 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 45 243 3 5 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 45 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 45 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 45 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 243 3 4 15 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 243
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 45 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 45 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 243 9 1 5 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 45 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 45 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 45 243 3 2 15 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 45 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 45 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 243 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 45 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 243 3 1 15 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 45 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 45 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 45 243))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 243
  (allA_succ_of_accept 43 44 243 (accept_3_4 43 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  44 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 44 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 243 (accept_3_4 40 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 44 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 44 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 44 243 (accept_3_4 37 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  44 243 (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 44 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 243 (accept_3_4 34 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 44 243 (Polychromatic418967fa.accept_20_13_4_3_1_14612 33 44 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 44 243 (accept_3_4 31 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  44 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 44 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 243 (accept_3_4 28 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 44 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 44 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 243
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 26 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 44 243 (accept_3_4 25 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  44 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 44 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 243 (accept_3_4 22 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 44 243 (Polychromatic418967fa.accept_14_7_2_5_1_4528 21 44 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 243
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 20 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 44 243 (accept_3_4 19 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  44 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 44 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 243 (accept_3_4 16 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 44 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 44 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 243
  (Polychromatic418967fa.accept_13_1_5_9_1_226 14 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 44 243 (accept_3_4 13 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  44 243 (Polychromatic418967fa.accept_17_12_10_5_1_4756 12 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 44 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 243 (accept_3_4 10 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 44 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 44 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 243
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 8 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 44 243 (accept_3_4 7 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44
  243 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 44 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 44 243 (accept_3_4 4 44 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 44 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 44 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 44 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 2
  44 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 243 (accept_3_4 1 44 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44 243)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43
  243 (allA_succ_of_accept 42 43 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 43 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 243 (accept_3_5 41 43 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 243 (accept_3_5 38 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 243 (Polychromatic418967fa.accept_28_9_15_19_1_14611 37 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 243 (Polychromatic418967fa.accept_19_17_5_15_1_7921 36 43 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 243 (accept_3_5 35 43 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 43 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 243 (accept_3_5 32 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 243 (Polychromatic418967fa.accept_16_14_11_3_1_4249 30 43 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 243 (accept_3_5 29 43 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 243 (accept_3_5 26 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 243 (accept_3_5 23 43 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 43 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 243 (accept_3_5 20 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 243 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 43 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 243 (accept_3_5 17 43 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 243
  (Polychromatic418967fa.accept_16_15_11_3_1_2179 15 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 243 (accept_3_5 14 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 243 (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 43 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 243 (accept_3_5 11 43 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 43 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 243
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 243 (accept_3_5 8 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  243 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 43 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 43 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 243 (accept_3_5 5 43 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 43 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 43 243 (accept_3_5 2 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43
  243 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 43 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 43 243))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 243 (allA_succ_of_accept 41 42
  243 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 42 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 42 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 243 3 13 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 38
  42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 243 3 12 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 42 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 42 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 243 3 11 14 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 243
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 42 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 243 3 10 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 42
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 42 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 42 243 3 9 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 42 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 42 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 42 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 243 3 8 14 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 243
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 42 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 42 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 243 3 7 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 42 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 243
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 243 3 6 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 42 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 42 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 243 3 5 14 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 42 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 42 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 42 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 243 3 4 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 42 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 42 243
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 42 243 3 3 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 42 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 42 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 243 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 42 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 243 3 2 14 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 42 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 243 3 1 14 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 42 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 42 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 243)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 243 (allA_succ_of_accept 40 41 243
  (accept_3_4 40 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 41 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 243 (accept_3_4 37 41 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 243
  (Polychromatic418967fa.accept_19_16_3_15_1_14603 35 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 41 243 (accept_3_4 34 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 41 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 41 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 243 (accept_3_4 31 41 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 243 (accept_3_4 28 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 243 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 243 (accept_3_4 25 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 243 (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 41 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 243
  (Polychromatic418967fa.accept_15_8_11_3_1_3847 23 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 243 (accept_3_4 22 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 243 (accept_3_4 19 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 41 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 243
  (Polychromatic418967fa.accept_19_17_3_15_1_9284 17 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 243 (accept_3_4 16 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 243 (accept_3_4 13 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 41 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 243 (accept_3_4 10 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 243 (accept_3_4 7 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 41 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 243
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 243 (accept_3_4 4 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 41 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 41 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 243 (accept_3_4 1 41 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 41 243))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 243 (allA_succ_of_accept
  39 40 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 40 243 (accept_3_5 38 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 40 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 40 243 (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 40
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 243 (accept_3_5 35 40 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 243 (Polychromatic418967fa.accept_13_8_1_9_1_1178
  34 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 243
  (Polychromatic418967fa.accept_18_15_4_9_1_4204 33 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 243 (accept_3_5 32 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 40 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 243 (accept_3_5 29 40 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 28 40 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 243
  (Polychromatic418967fa.accept_16_11_8_3_1_3183 27 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 243 (accept_3_5 26 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 243 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 40 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 243 (accept_3_5 23 40 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 243 (Polychromatic418967fa.accept_15_7_10_3_1_2891 22 40
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 243
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 21 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 243 (accept_3_5 20 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 243 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 40 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 243 (accept_3_5 17 40 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 243 (Polychromatic418967fa.accept_25_16_15_18_1_14610 16 40 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 243
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 15 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 243 (accept_3_5 14 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 243 (Polychromatic418967fa.accept_16_12_8_3_1_4241 12 40 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 243 (accept_3_5 11 40 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 243 (Polychromatic418967fa.accept_13_10_1_9_1_3380 10 40
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 243
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 243 (accept_3_5 8 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 243 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 40 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 243 (accept_3_5 5 40 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 243 (Polychromatic418967fa.accept_16_4_8_3_1_4206 4 40 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 243 (Polychromatic418967fa.accept_14_3_12_5_1_153 3
  40 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 243 (accept_3_5 2 40 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  243)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 243 (allA_succ_of_accept 38 39 243
  (Polychromatic418967fa.accept_11_5_6_1_1_988 38 39 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 39 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 243 3 12 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 243 (Polychromatic418967fa.accept_15_5_9_3_1_528 35
  39 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 39 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 243 3 11 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 243 (Polychromatic418967fa.accept_18_14_3_9_1_4234 32 39 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 243 (Polychromatic418967fa.accept_16_15_7_3_1_4273 31 39
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 243 3 10 13 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 39 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 39 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 243 3 9 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 26 39 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 243
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 39 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 243 3 8 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 39 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 39 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 243 3 7 13 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 39 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 243 (Polychromatic418967fa.accept_18_1_3_9_1_328 19 39 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 243 3 6 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 243 (Polychromatic418967fa.accept_19_17_1_15_1_7901 17 39
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 39 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 243 3 5 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 243 (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 39 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 39 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 243 3 4 13 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 243
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 11 39 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 243 (Polychromatic418967fa.accept_15_10_9_3_1_1947 10 39 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 243 3 3 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 39 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 243
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 39 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 243 3 2 13 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 39 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 39 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 243 3 1 13 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 243
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 39 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 39 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 243))))))))))))))))))))))))))))))))))))))) (allB_succ 38 243
  (allA_succ_of_accept 37 38 243 (accept_3_4 37 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 38 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 243 (accept_3_4 34 38 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 38 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 243
  (Polychromatic418967fa.accept_25_7_13_18_1_14609 32 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 38 243 (accept_3_4 31 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 38 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 38 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 38 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 38 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 243 (accept_3_4 28 38 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 243 (Polychromatic418967fa.accept_15_12_8_3_1_1995
  27 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 243
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 243 (accept_3_4 25 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 243 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 38 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 243 (accept_3_4 22 38 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 38 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 243
  (Polychromatic418967fa.accept_15_5_8_3_1_556 20 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 243 (accept_3_4 19 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 38 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 243 (accept_3_4 16 38 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 38 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 243
  (Polychromatic418967fa.accept_25_14_13_18_1_14608 14 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 38 243 (accept_3_4 13 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 38 243 (Polychromatic418967fa.accept_14_12_10_5_1_2712 12 38 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 38 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 38 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 243 (accept_3_4 10 38 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 38
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 243 (accept_3_4 7 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  243 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 38 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 38 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 243 (accept_3_4 4 38 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 243 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 38 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 38
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 243 (accept_3_4 1 38 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 243)))))))))))))))))))))))))))))))))))))) (allB_succ 37 243
  (allA_succ_of_accept 36 37 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 37 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 243 (accept_3_5 35 37 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 37 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 243 (Polychromatic418967fa.accept_12_9_1_3_1_350
  33 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 243 (accept_3_5 32
  37 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 37 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 243 (accept_3_5 29 37 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 243 (Polychromatic418967fa.accept_13_1_11_9_1_1857
  27 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 243 (accept_3_5 26
  37 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 243 (accept_3_5 23 37 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 37 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 243 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 243 (accept_3_5 20
  37 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 243
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 37 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 243 (accept_3_5 17 37 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 243 (Polychromatic418967fa.accept_10_5_7_3_1_561
  15 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 243 (accept_3_5 14
  37 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 243
  (Polychromatic418967fa.accept_25_13_12_18_1_14607 13 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 243 (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 37 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 243 (accept_3_5 11 37 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 37 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 243
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 243 (accept_3_5 8 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  243 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 37 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 37 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 243 (accept_3_5 5 37 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 37 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 37 243 (accept_3_5 2 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37
  243 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 37 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 37 243))))))))))))))))))))))))))))))))))))) (allB_succ 36 243 (allA_succ_of_accept 35 36 243
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 36 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 36 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 243 3 11 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 32
  36 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 243 3 10 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 36 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 36 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 243 9 3 4 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 243
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 36 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 36 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 243 3 8 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 36 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 243
  (Polychromatic418967fa.accept_16_6_4_3_1_2189 22 36 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 36 243 3 7 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 36 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 36 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 243 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 36 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 243 9 2 4 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 36 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 36 243 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 36 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 243 3 5 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 243 (Polychromatic418967fa.accept_13_1_10_9_1_215 14 36 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 243
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 243 3 4 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 36 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 36 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 243 9 1 4 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 243
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 36 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 36 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 36 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 243 3 2 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 36 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 36 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 36 243 3 1 12 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 36 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 36 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 243 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 36 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 243))))))))))))))))))))))))))))))))))))
  (allB_succ 35 243 (allA_succ_of_accept 34 35 243 (accept_3_4 34 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 35 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 35 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 243 (accept_3_4 31 35 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 243 (Polychromatic418967fa.accept_14_2_7_5_1_5450
  30 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 243
  (Polychromatic418967fa.accept_20_9_15_3_1_7470 29 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 243 (accept_3_4 28 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 35 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 243 (accept_3_4 25 35 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 35 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 243
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 243 (accept_3_4 22 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 243 (accept_3_4 19 35 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 35 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 243 (accept_3_4 16 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 243 (Polychromatic418967fa.accept_18_15_17_9_1_4200 15 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 35 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 243 (accept_3_4 13 35 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 243 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 35 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 243
  (Polychromatic418967fa.accept_19_11_16_15_1_11951 11 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 35 243 (accept_3_4 10 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 35 243 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 35 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 243 (accept_3_4 7 35 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 243 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6
  35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 243
  (Polychromatic418967fa.accept_20_5_15_3_1_4516 5 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 243 (accept_3_4 4 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  243 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 35 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 35 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 243 (accept_3_4 1 35 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 243))))))))))))))))))))))))))))))))))) (allB_succ 34 243 (allA_succ_of_accept 33 34 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 243 (accept_3_5 32 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 34 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 243 (accept_3_5 29 34 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 243 (Polychromatic418967fa.accept_20_8_14_3_1_9074 28 34
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 243
  (Polychromatic418967fa.accept_10_7_4_3_1_560 27 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 243 (accept_3_5 26 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 243 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 34 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 243 (accept_3_5 23 34 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 34 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 243 (accept_3_5 20 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 34 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 243 (accept_3_5 17 34 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 16 34 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 243 (accept_3_5 14 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 34 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 243 (accept_3_5 11 34 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 243 (Polychromatic418967fa.accept_23_10_11_13_1_14606 10 34
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 243 (accept_3_5 8 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 34 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 243 (accept_3_5 5 34 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 34 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3
  34 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 243 (accept_3_5 2 34 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 34
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 243))))))))))))))))))))))))))))))))))
  (allB_succ 33 243 (allA_succ_of_accept 32 33 243 (Polychromatic418967fa.accept_13_6_7_9_1_1848 32 33 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 243
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 33 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 243 3 10 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 33 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 243 (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 33 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 243 3 9 11 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 33 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 33 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 243 3 8 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 33 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 33 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 243 3 7 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 243 (Polychromatic418967fa.accept_16_4_1_3_1_6581 20 33 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 33 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 243 3 6 11 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 33 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 16 33 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 243 3 5 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 33 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 33 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 243 3 4 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 33 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 33 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 243 3 3 11 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 243
  (Polychromatic418967fa.accept_13_8_7_9_1_611 8 33 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 33 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 243 3 2 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 33 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 243
  (Polychromatic418967fa.accept_13_4_7_9_1_5260 4 33 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 243 3 1 11 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 33 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 33 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 243)))))))))))))))))))))))))))))))))
  (allB_succ 32 243 (allA_succ_of_accept 31 32 243 (accept_3_4 31 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 32 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 243 (accept_3_4 28 32 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 27
  32 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 243
  (Polychromatic418967fa.accept_19_7_13_15_1_2407 26 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 243 (accept_3_4 25 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 243 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 243 (accept_3_4 22 32 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 32 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 243 (accept_3_4 19 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 243 (accept_3_4 16 32 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 32 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 243
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 14 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 243 (accept_3_4 13 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 243 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 243 (accept_3_4 10 32 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 32 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 243 (accept_3_4 7 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  243 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 32 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 243 (accept_3_4 4 32 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 243 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 32 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  32 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 243 (accept_3_4 1 32 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 243)))))))))))))))))))))))))))))))) (allB_succ 31 243
  (allA_succ_of_accept 30 31 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 31 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 243 (accept_3_5 29 31 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 243 (Polychromatic418967fa.accept_13_1_5_9_1_226
  27 31 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 243 (accept_3_5 26
  31 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 243
  (Polychromatic418967fa.accept_19_6_12_15_1_7895 25 31 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 243 (Polychromatic418967fa.accept_18_6_13_9_1_4218 24 31 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 243 (accept_3_5 23 31 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 31 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 243 (Polychromatic418967fa.accept_11_10_9_1_1_2186
  21 31 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 243 (accept_3_5 20
  31 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 243
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 31 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 243 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 31 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 243 (accept_3_5 17 31 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  31 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 243 (accept_3_5 14 31
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 243
  (Polychromatic418967fa.accept_15_13_1_3_1_1972 13 31 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 31 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 243 (accept_3_5 11 31 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 31 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 31
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 243 (accept_3_5 8 31 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 243 (Polychromatic418967fa.accept_16_7_15_3_1_1302
  7 31 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 243
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 31 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 243 (accept_3_5 5 31 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 31 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 243 (accept_3_5 2 31 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 31 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 243))))))))))))))))))))))))))))))) (allB_succ 30 243
  (allA_succ_of_accept 29 30 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 30 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 30 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 243 3 9 10 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 243
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 30 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 30 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 243 3 8 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 243 (Polychromatic418967fa.accept_18_5_12_9_1_6871 23 30 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 243
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 30 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 243 3 7 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 30 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 243 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 30 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 243 3 6 10 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 30 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 30 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 243 3 5 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 30 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 30 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 243 3 4 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 30 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 30 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 243 3 3 10 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 30 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 243 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 30 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 243 3 2 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 30 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 243
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 30 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 243 3 1 10 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 30 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 30 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 243)))))))))))))))))))))))))))))) (allB_succ
  29 243 (allA_succ_of_accept 28 29 243 (accept_3_4 28 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 29 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 29 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 243 (accept_3_4 25 29 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 24
  29 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 243
  (Polychromatic418967fa.accept_19_4_10_15_1_9243 23 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 243 (accept_3_4 22 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 243 (accept_3_4 19 29 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 29 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 243 (accept_3_4 16 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 243 (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 29 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 243 (accept_3_4 13 29 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 29 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 243 (accept_3_4 10 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 243 (accept_3_4 7 29 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 29 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 243
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 243 (accept_3_4 4 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 29 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 29 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 243 (accept_3_4 1 29 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 243))))))))))))))))))))))))))))) (allB_succ 28 243 (allA_succ_of_accept 27 28 243
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 243 (accept_3_5 26 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 243 (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 28 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 243 (accept_3_5 23 28 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 243 (Polychromatic418967fa.accept_19_3_9_15_1_9240 22 28
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 243
  (Polychromatic418967fa.accept_10_1_8_3_1_947 21 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 243 (accept_3_5 20 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 243 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 28 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 243 (accept_3_5 17 28 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 28 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 243
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 243 (accept_3_5 14 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 243 (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 28 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 243 (accept_3_5 11 28 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 243 (Polychromatic418967fa.accept_15_10_13_3_1_4816 10 28
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 243
  (Polychromatic418967fa.accept_15_9_13_3_1_535 9 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 243 (accept_3_5 8 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 243 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 28 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 243 (accept_3_5 5 28 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 243 (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 28 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3
  28 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 243 (accept_3_5 2 28 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 243))))))))))))))))))))))))))))
  (allB_succ 27 243 (allA_succ_of_accept 26 27 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 27 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 25 27 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 243 3 8 9 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 243 (Polychromatic418967fa.accept_13_10_1_9_1_3380 23 27 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 27 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 243 3 7 9 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 243
  (Polychromatic418967fa.accept_14_6_13_5_1_534 20 27 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 243 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 27 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 243 9 2 3 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 27 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 243
  (Polychromatic418967fa.accept_10_6_7_3_1_547 16 27 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 243 3 5 9 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 243 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 27 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 243 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 27
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 243 3 4 9 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 243
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 27 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 243 (Polychromatic418967fa.accept_13_10_1_9_1_3380 10 27 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 243 9 1 3 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 27 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 243
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 27 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 243 3 2 9 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 27 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 27 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 243 3 1 9 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 243
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 2 27 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 27 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 243))))))))))))))))))))))))))) (allB_succ 26 243 (allA_succ_of_accept 25
  26 243 (accept_3_4 25 26 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 243
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 26 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 26 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 243 (accept_3_4 22 26 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 26 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 243
  (Polychromatic418967fa.accept_25_20_1_18_1_14605 20 26 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 26 243 (accept_3_4 19 26 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 26 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 26 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 26 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 26 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 243 (accept_3_4 16 26 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 243
  (Polychromatic418967fa.accept_21_15_5_12_1_3987 15 26 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 26 243 (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 26 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 243 (accept_3_4 13 26 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 26 243 (Polychromatic418967fa.accept_16_12_10_3_1_4209 12 26 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 26 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 243 (accept_3_4 10 26 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 26 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 26 243 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 26 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 243 (accept_3_4 7 26 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 26 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 26 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 26
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 243 (accept_3_4 4 26 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26 243 (Polychromatic418967fa.accept_14_3_12_5_1_153 3
  26 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 243
  (Polychromatic418967fa.accept_23_2_3_13_1_14604 2 26 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 26 243 (accept_3_4 1 26 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  243)))))))))))))))))))))))))) (allB_succ 25 243 (allA_succ_of_accept 24 25 243
  (Polychromatic418967fa.accept_11_2_3_1_1_244 24 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 243 (accept_3_5 23 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 25 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 243 (accept_3_5 20 25 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 243 (Polychromatic418967fa.accept_21_19_4_12_1_4027 19 25 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 243 (accept_3_5 17 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 25 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 243 (accept_3_5 14 25 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 243
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 243 (accept_3_5 11 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 25 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 243 (accept_3_5 8 25 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 25 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 243 (accept_3_5 5 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 243 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 25 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 243 (accept_3_5 2 25 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 243))))))))))))))))))))))))) (allB_succ 24 243
  (allA_succ_of_accept 23 24 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 24 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 24 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 243 3 7 8 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 243
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 20 24 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 24 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 243 3 6 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 24 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 16 24 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 243 3 5 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 24 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 243 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 24
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 243 3 4 8 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 243
  (Polychromatic418967fa.accept_16_11_8_3_1_3183 11 24 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 24 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 243 3 3 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 24 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 243
  (Polychromatic418967fa.accept_10_7_4_3_1_560 7 24 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 243 3 2 8 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 243 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 24 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 243 (Polychromatic418967fa.accept_16_4_8_3_1_4206 4 24 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 243 3 1 8 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 243
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 24 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 243)))))))))))))))))))))))) (allB_succ 23 243 (allA_succ_of_accept 22 23
  243 (accept_3_4 22 23 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 243
  (Polychromatic418967fa.accept_12_9_11_3_1_772 21 23 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 243 (accept_3_4 19 23 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 23 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  23 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 243 (accept_3_4 16 23
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 243
  (Polychromatic418967fa.accept_16_15_7_3_1_4273 15 23 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 23 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 243 (accept_3_4 13 23 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 23 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 11
  23 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 243 (accept_3_4 10 23
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 243
  (Polychromatic418967fa.accept_12_9_11_3_1_772 9 23 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 243 (accept_3_4 7 23 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 243 (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 23 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 243 (Polychromatic418967fa.accept_15_5_8_3_1_556 5
  23 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 243 (accept_3_4 4 23 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  23 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 243
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 23 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 243 (accept_3_4 1 23 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  243))))))))))))))))))))))) (allB_succ 22 243 (allA_succ_of_accept 21 22 243 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 22 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 243 (accept_3_5 20
  22 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 22 243
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 22 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 22 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 22 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 243 (accept_3_5 17 22 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 22 243 (Polychromatic418967fa.accept_19_16_3_15_1_14603 16 22 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 243
  (Polychromatic418967fa.accept_10_5_2_3_1_239 15 22 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 243 (accept_3_5 14 22 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 22 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 243 (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 22 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 243 (accept_3_5 11 22 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 22 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 22 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 243 (accept_3_5 8 22 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 22 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 22 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 243 (accept_3_5 5 22 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 22 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 22
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 243 (accept_3_5 2 22 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 22
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 243)))))))))))))))))))))) (allB_succ 21
  243 (allA_succ_of_accept 20 21 243 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 21 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 243 (Polychromatic418967fa.accept_12_7_9_3_1_767
  19 21 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 243 3 6 7 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 21 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134 16 21 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 243 3 5 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 21 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 243
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 21 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 243 3 4 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 243 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 21 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 21 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 243 3 3 7 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 243
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 21 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 21 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 243 3 2 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 21 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 243
  (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 21 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 243 3 1 7 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 21 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 21 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 243))))))))))))))))))))) (allB_succ 20 243
  (allA_succ_of_accept 19 20 243 (accept_3_4 19 20 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 20 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 243 (accept_3_4 16 20 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 20 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 243
  (Polychromatic418967fa.accept_19_14_1_15_1_7914 14 20 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 243 (accept_3_4 13 20 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 243 (Polychromatic418967fa.accept_16_12_4_3_1_4295 12 20 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 243 (accept_3_4 10 20 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 243 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 20 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 20 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 243 (accept_3_4 7 20 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  243 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 20 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 243 (accept_3_4 4 20 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 20 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 243 (Polychromatic418967fa.accept_13_2_7_9_1_2616 2
  20 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 243 (accept_3_4 1 20 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 243)))))))))))))))))))) (allB_succ 19 243 (allA_succ_of_accept
  18 19 243 (Polychromatic418967fa.accept_21_18_19_12_1_3982 18 19 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 243 (accept_3_5 17 19 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 19 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 243 (accept_3_5 14 19 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 243
  (Polychromatic418967fa.accept_31_13_19_26_1_14602 13 19 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 19 243 (Polychromatic418967fa.accept_22_12_19_1_1_14601 12 19 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 19 243 (accept_3_5 11 19 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 19 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 19 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 19 243
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 19 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 19 243 (accept_3_5 8 19 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 19
  243 (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 19 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 19 243 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 19 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 19 243 (accept_3_5 5 19 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 19 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 19 243
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 19 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 19 243 (accept_3_5 2 19 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 19
  243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 19 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 19 243))))))))))))))))))) (allB_succ 18 243 (allA_succ_of_accept 17 18 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 18 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 18 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 18 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 243 3 5 6 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 18 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 18 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 243 3 4 6 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 243 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 18 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 243 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 18 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 243 9 1 2 27 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 18 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 243 (Polychromatic418967fa.accept_19_7_18_15_1_5061 7 18 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 243 3 2 6 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 18 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 18 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 243 3 1 6 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 18 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 18 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 243)))))))))))))))))) (allB_succ 17 243
  (allA_succ_of_accept 16 17 243 (accept_3_4 16 17 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 17 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 17 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 243 (accept_3_4 13 17 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 243 (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 17 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 243
  (Polychromatic418967fa.accept_23_11_17_13_1_13025 11 17 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 17 243 (accept_3_4 10 17 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 17 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 17 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 243 (accept_3_4 7 17 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 17
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 17 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 243 (accept_3_4 4 17 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  243 (Polychromatic418967fa.accept_19_3_17_15_1_6459 3 17 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 17 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 17 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 243 (accept_3_4 1 17 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 17 243))))))))))))))))) (allB_succ 16 243 (allA_succ_of_accept 15 16 243
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 16 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 243 (accept_3_5 14 16 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 16 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 243 (accept_3_5 11 16 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 16 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 243
  (Polychromatic418967fa.accept_10_9_6_3_1_545 9 16 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 243 (accept_3_5 8 16 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 16 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 243 (accept_3_5 5 16 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 16 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  16 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 243 (accept_3_5 2 16 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 243)))))))))))))))) (allB_succ 15 243
  (allA_succ_of_accept 14 15 243 (Polychromatic418967fa.accept_13_1_2_9_1_1186 14 15 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 15 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 243 3 4 5 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 15 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 15 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 243 3 3 5 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 15 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 15 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 243 3 2 5 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 243 (Polychromatic418967fa.accept_13_5_2_9_1_1195 5 15 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 15 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 243 3 1 5 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 243
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 15 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 243 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 15 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 243))))))))))))))) (allB_succ 14 243 (allA_succ_of_accept 13 14 243
  (accept_3_4 13 14 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 243
  (Polychromatic418967fa.accept_25_12_14_18_1_14600 12 14 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 14 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 14 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 243 (accept_3_4 10 14 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 14 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 14 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 243
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 8 14 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 14 243 (accept_3_4 7 14 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14
  243 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 14 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 14 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 243 (accept_3_4 4 14 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 243 (Polychromatic418967fa.accept_18_3_14_9_1_4264 3 14 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 243 (Polychromatic418967fa.accept_11_2_3_1_1_244 2
  14 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 243 (accept_3_4 1 14 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 243)))))))))))))) (allB_succ 13 243 (allA_succ_of_accept 12 13
  243 (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 13 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 243 (accept_3_5 11 13 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 13 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 13 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 243 (accept_3_5 8 13 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 243 (Polychromatic418967fa.accept_19_7_13_15_1_2407
  7 13 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 13 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 243 (accept_3_5 5 13 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 13 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 243 (accept_3_5 2 13 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 243))))))))))))) (allB_succ 12 243 (allA_succ_of_accept 11 12
  243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 12 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 12 243 (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 12 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 243 3 3 4 81 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 243
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 8 12 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 12 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 243 3 2 4 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 243 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 12 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 243
  (Polychromatic418967fa.accept_16_4_12_3_1_2180 4 12 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 12 243 3 1 4 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 12 243 (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 12 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 243 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 12 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 243)))))))))))) (allB_succ 11 243
  (allA_succ_of_accept 10 11 243 (accept_3_4 10 11 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  11 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 11 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 11 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 243 (accept_3_4 7 11 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 11 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 243
  (Polychromatic418967fa.accept_19_5_11_15_1_2460 5 11 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 11 243 (accept_3_4 4 11 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11
  243 (Polychromatic418967fa.accept_21_3_11_12_1_10183 3 11 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 11 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 11 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 243 (accept_3_4 1 11 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 11 243))))))))))) (allB_succ 10 243 (allA_succ_of_accept 9 10 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 10 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 243 (accept_3_5 8 10 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 10 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 243 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 10 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 243 (accept_3_5 5 10 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 243 (Polychromatic418967fa.accept_19_4_10_15_1_9243 4 10 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 243 (Polychromatic418967fa.accept_19_3_10_15_1_9241
  3 10 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 243 (accept_3_5 2 10
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  10 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 243)))))))))) (allB_succ 9 243
  (allA_succ_of_accept 8 9 243 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 9 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 243 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 9 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 243 3 2 3 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 243
  (Polychromatic418967fa.accept_12_5_9_3_1_85 5 9 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 9 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 243 3 1 3 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 9 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 243
  (Polychromatic418967fa.accept_12_1_9_3_1_370 1 9 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 243))))))))) (allB_succ 8 243 (allA_succ_of_accept 7 8 243 (accept_3_4 7 8 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 8 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 243
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 243 (accept_3_4 4 8 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 8 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 243 (Polychromatic418967fa.accept_19_2_8_15_1_2447 2 8 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 243 (accept_3_4 1 8 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 243)))))))) (allB_succ 7 243 (allA_succ_of_accept 6 7 243
  (Polychromatic418967fa.accept_10_6_7_3_1_547 6 7 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 243 (accept_3_5 5 7 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 243
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 243 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 7 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 243 (accept_3_5 2 7 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 243 (Polychromatic418967fa.accept_21_1_7_12_1_1465 1 7 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 243))))))) (allB_succ 6 243 (allA_succ_of_accept 5 6 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 6 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 6 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 243 3 1 2 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 243 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 6 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 6 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 243)))))) (allB_succ 5 243 (allA_succ_of_accept 4 5 243 (accept_3_4 4 5 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 243 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 5 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 5
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 243 (accept_3_4 1 5 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 243))))) (allB_succ 4 243 (allA_succ_of_accept 3 4 243
  (Polychromatic418967fa.accept_21_3_4_12_1_1462 3 4 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 243 (accept_3_5 2 4 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 243
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 243)))) (allB_succ 3 243 (allA_succ_of_accept 2 3 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 3 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 3 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 243))) (allB_succ 2 243 (allA_succ_of_accept 1 2 243 (accept_3_4 1 2 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 243)) (allB_two
  243))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


