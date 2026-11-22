-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch213_Segment000
-- name    : Polychromatic418967fa_Branch213_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:32:29.517078+00:00
-- url     : https://prove2.me/theorems/8494ef57-3512-44e9-8df3-cbb8a49f8992
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

def Polychromatic418967fa.branch_213_segment_000 : allB 100 213 :=
  allB_succ 99 213 (allA_succ_of_accept 98 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 213
  (Polychromatic418967fa.accept_12_1_3_9_1_174 97 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 213 3 32 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 95 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 213 3 31 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 213
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 92 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 91 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 213 3 30 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 89
  99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 88 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 213 3 29 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 85 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 213 3 28 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 213
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 83 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 213 3 27 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 213 (Polychromatic418967fa.accept_15_5_9_3_1_528 80
  99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 79 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 213 3 26 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 213 (Polychromatic418967fa.accept_10_6_9_3_1_935 76 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 213 3 25 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 73 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 213 3 24 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  71 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 213 3 23 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 213 3 22 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 213 (Polychromatic418967fa.accept_10_4_9_3_1_1907 64 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 213 3 21 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 213 3 20 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 213 3 19 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 213
  (Polychromatic418967fa.accept_10_6_9_3_1_935 56 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 213 3 18 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 53
  99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 213
  (Polychromatic418967fa.accept_18_16_9_15_1_4614 52 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 213 3 17 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 213 3 16 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 213 3 15 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 213 3 14 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 213 3 13 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 213 3 12 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 213 3 11 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 213 3 10 33 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 213
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 213 (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 213 3 9 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 213 3 8 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 213 3 7 33 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 213
  (Polychromatic418967fa.accept_15_5_9_3_1_528 20 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 213 3 6 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 213 3 5 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 213 3 4 33 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 213 3 3 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 213 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 213 3 2 33 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 99 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 213 3 1 33 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 99 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  213 (allA_succ_of_accept 97 98 213 (accept_3_4 97 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 96 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 213 (accept_3_4 94 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 93 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 92 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 213 (accept_3_4 91 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 90 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 213 (accept_3_4 88 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 86 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 213 (accept_3_4 85 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 84 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 213 (accept_3_4 82 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 213 (Polychromatic418967fa.accept_10_1_8_3_1_947 81 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 213
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 80 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 213 (accept_3_4 79 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 78 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 213 (accept_3_4 76 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 213 (accept_3_4 73 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 213 (Polychromatic418967fa.accept_15_12_8_3_1_1995 72 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 213 (accept_3_4 70 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 213 (Polychromatic418967fa.accept_15_9_8_3_1_557 69 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 68 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 213 (accept_3_4 67 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 213 (accept_3_4 64 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 213
  (Polychromatic418967fa.accept_20_2_18_13_1_3843 62 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 213 (accept_3_4 61 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 213 (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 213 (accept_3_4 58 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 213 (accept_3_4 55 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 213 (accept_3_4 52 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 213 (accept_3_4 49 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 213 (accept_3_4 46 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 213 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 213
  (Polychromatic418967fa.accept_17_10_13_9_1_3913 44 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 213 (accept_3_4 43 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 213 (accept_3_4 40 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 213 (accept_3_4 37 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 213 (accept_3_4 34 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 213 (Polychromatic418967fa.accept_17_16_13_9_1_11391 33 98 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 213 (accept_3_4 31 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 213 (accept_3_4 28 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 213
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 213 (accept_3_4 25 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 213 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 213 (accept_3_4 22 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 213 (accept_3_4 19 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 213 (accept_3_4 16 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 213 (accept_3_4 13 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 213 (accept_3_4 10 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 213 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 98 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 213
  (Polychromatic418967fa.accept_19_8_3_4_1_9865 8 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 213 (accept_3_4 7 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  213 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 98 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 213 (accept_3_4 4 98 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 98
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 213 (accept_3_4 1 98 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  213 (allA_succ_of_accept 96 97 213 (Polychromatic418967fa.accept_10_6_7_3_1_547 96 97 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 213 (accept_3_5 95 97 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 93
  97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 213 (accept_3_5 92 97
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 213 (Polychromatic418967fa.accept_9_1_7_6_1_75
  91 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 97 213
  (Polychromatic418967fa.accept_11_2_9_4_1_310 90 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 97 213 (accept_3_5 89 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 97 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 87 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 213 (accept_3_5 86 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 85 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 84 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 213 (accept_3_5 83 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 213 (accept_3_5 80 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 213
  (Polychromatic418967fa.accept_30_18_7_3_1_8262 78 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 213 (accept_3_5 77 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 213 (accept_3_5 74 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 213 (accept_3_5 71 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 213 (Polychromatic418967fa.accept_13_4_6_5_1_2333 69 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 213 (accept_3_5 68 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 213 (accept_3_5 65 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 213 (accept_3_5 62 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 213 (Polychromatic418967fa.accept_16_13_1_5_1_5469 61 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 213 (accept_3_5 59 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 57 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 213 (accept_3_5 56 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 213
  (Polychromatic418967fa.accept_10_4_7_3_1_54 54 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 213 (accept_3_5 53 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 213 (accept_3_5 50 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 213 (accept_3_5 47 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 213 (accept_3_5 44 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 213 (Polychromatic418967fa.accept_13_4_6_5_1_2333 43 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 213
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 42 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 213 (accept_3_5 41 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 213 (accept_3_5 38 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 213 (accept_3_5 35 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 213 (Polychromatic418967fa.accept_19_14_2_4_1_8473 33 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 213 (accept_3_5 32 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 97 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 213 (accept_3_5 29 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 213 (accept_3_5 26 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 213
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 213 (accept_3_5 23 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 213 (accept_3_5 20 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 213 (accept_3_5 17 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 213 (accept_3_5 14 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 213 (accept_3_5 11 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 213 (accept_3_5 8 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 213 (Polychromatic418967fa.accept_19_7_2_4_1_12590 7 97 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 213
  (Polychromatic418967fa.accept_10_6_7_3_1_547 6 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 213 (accept_3_5 5 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 97 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 213 (accept_3_5 2 97 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 97 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 213
  (allA_succ_of_accept 95 96 213 (Polychromatic418967fa.accept_11_7_8_4_1_718 95 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 213 (Polychromatic418967fa.accept_18_4_6_15_1_2250 94 96
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 96 213 3 31 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 96 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 92 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 96 213 (Polychromatic418967fa.accept_15_1_6_3_1_2827 91 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 213 3 30 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 213 (Polychromatic418967fa.accept_10_9_6_3_1_545 89
  96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 96 213
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 88 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 96 213 3 29 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 96 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 86 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 213 3 28 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 213
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 83 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 213 (Polychromatic418967fa.accept_18_10_6_15_1_3412 82 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 213 3 27 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 213 (Polychromatic418967fa.accept_15_5_6_3_1_525 80
  96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 79 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 213 3 26 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 96 213 (Polychromatic418967fa.accept_10_7_6_3_1_927 77 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 213 (Polychromatic418967fa.accept_15_1_6_3_1_2827 76 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 96 213 3 25 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 96 213
  (Polychromatic418967fa.accept_19_17_1_4_1_7022 74 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 96 213 (Polychromatic418967fa.accept_11_7_8_4_1_718 73 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 213 3 24 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 71
  96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 213
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 70 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 96 213 3 23 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 96 213 (Polychromatic418967fa.accept_10_8_6_3_1_1394 68 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 213 (Polychromatic418967fa.accept_10_7_6_3_1_927 67 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 213 3 22 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 213 3 21 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 213 (Polychromatic418967fa.accept_11_7_8_4_1_718 62
  96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 213
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 61 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 213 3 20 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 213 (Polychromatic418967fa.accept_10_9_6_3_1_545 59 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 96 213 3 19 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 96 213
  (Polychromatic418967fa.accept_11_1_8_4_1_717 56 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 96 213 (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 213 3 18 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 213 (Polychromatic418967fa.accept_17_2_11_9_1_1739
  53 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 213
  (Polychromatic418967fa.accept_18_16_6_15_1_3376 52 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 96 213 3 17 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 96 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 213 (Polychromatic418967fa.accept_10_9_6_3_1_545 49 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 213 3 16 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 213
  (Polychromatic418967fa.accept_10_7_6_3_1_927 47 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 213 (Polychromatic418967fa.accept_15_1_6_3_1_2827 46 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 213 3 15 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 44
  96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 213 3 14 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 213 (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 213 (Polychromatic418967fa.accept_11_7_8_4_1_718 40 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 213 3 13 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 213
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 213 3 12 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 213 (Polychromatic418967fa.accept_15_5_6_3_1_525 35
  96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 213
  (Polychromatic418967fa.accept_11_1_8_4_1_717 34 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 96 213 3 11 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 96 213 (Polychromatic418967fa.accept_21_11_12_3_1_6461 32 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 213 (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 213 3 10 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 213 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 213 3 9 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 213 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 213
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 213 3 8 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 213 3 7 32 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 213
  (Polychromatic418967fa.accept_15_5_6_3_1_525 20 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 213 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 213 3 6 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 213 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 96 213 3 5 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 96 213 (Polychromatic418967fa.accept_21_14_12_3_1_9637 14 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 213 (Polychromatic418967fa.accept_21_13_12_3_1_8028 13 96
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 213 3 4 32 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 213
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 213 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 213 3 3 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 213
  (Polychromatic418967fa.accept_10_7_6_3_1_927 7 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 213 3 2 32 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 213 (Polychromatic418967fa.accept_14_5_12_3_1_3397 5 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 213 (Polychromatic418967fa.accept_18_4_6_15_1_2250 4 96 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 213 3 1 32 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 96 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 213
  (allA_succ_of_accept 94 95 213 (accept_3_4 94 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 93 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 213 (accept_3_4 91 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 89 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 213 (accept_3_4 88 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 213 (Polychromatic418967fa.accept_10_7_5_3_1_542 87 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 213 (accept_3_4 85 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 83 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 213 (accept_3_4 82 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 213 (Polychromatic418967fa.accept_15_6_5_3_1_1988 81 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 213 (accept_3_4 79 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 213
  (Polychromatic418967fa.accept_10_7_5_3_1_542 77 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 213 (accept_3_4 76 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 213 (accept_3_4 73 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 213 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 213 (accept_3_4 70 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 213 (accept_3_4 67 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 213 (accept_3_4 64 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 213 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 213 (accept_3_4 61 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 213 (Polychromatic418967fa.accept_18_6_5_15_1_7292 60 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 213
  (Polychromatic418967fa.accept_37_22_21_28_1_12589 59 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 95 213 (accept_3_4 58 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 95 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 95 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 213 (accept_3_4 55 95 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 213 (accept_3_4 52 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 213 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 213 (accept_3_4 49 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 213 (accept_3_4 46 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 213 (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 213 (accept_3_4 43 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 213 (accept_3_4 40 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 213 (accept_3_4 37 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 213 (accept_3_4 34 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 213 (Polychromatic418967fa.accept_16_1_15_5_1_708 33 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 213 (accept_3_4 31 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 213 (accept_3_4 28 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 213 (accept_3_4 25 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 213 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 213
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 213 (accept_3_4 22 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 213 (accept_3_4 19 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 213 (accept_3_4 16 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 213 (accept_3_4 13 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 213 (accept_3_4 10 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 213 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 213 (accept_3_4 7 95 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 213
  (Polychromatic418967fa.accept_20_5_15_13_1_5235 5 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 213 (accept_3_4 4 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 95 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 213 (accept_3_4 1 95 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 213
  (allA_succ_of_accept 93 94 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 93 94 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 213 (accept_3_5 92 94 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 213 (Polychromatic418967fa.accept_11_2_6_4_1_3028
  90 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 213 (accept_3_5 89
  94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 213
  (Polychromatic418967fa.accept_9_7_4_6_1_273 88 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 213 (accept_3_5 86 94 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 84
  94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 213 (accept_3_5 83 94
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 213 (Polychromatic418967fa.accept_9_1_4_6_1_5
  82 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 94 213
  (Polychromatic418967fa.accept_18_9_4_15_1_555 81 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 94 213 (accept_3_5 80 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  94 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 94 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 78 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 213 (accept_3_5 77 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 213 (Polychromatic418967fa.accept_13_11_3_5_1_982 76 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 94 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 94 213 (accept_3_5 74 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  94 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 94 213 (Polychromatic418967fa.accept_19_15_18_4_1_9834 72 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 213 (accept_3_5 71 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 94 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 213
  (Polychromatic418967fa.accept_10_9_4_3_1_539 69 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 94 213 (accept_3_5 68 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  94 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 94 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 213 (accept_3_5 65 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 94 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 94 213 (accept_3_5 62 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  94 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 94 213 (Polychromatic418967fa.accept_13_8_3_5_1_1636 60 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 213 (accept_3_5 59 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 213 (Polychromatic418967fa.accept_13_6_3_5_1_3167 58 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 213 (accept_3_5 56 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 213 (accept_3_5 53 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 213 (accept_3_5 50 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 213 (accept_3_5 47 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 213
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 213 (accept_3_5 44 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 213 (accept_3_5 41 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 213 (Polychromatic418967fa.accept_13_1_3_5_1_140 40 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 213 (accept_3_5 38 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 213 (Polychromatic418967fa.accept_19_17_18_4_1_12571 36 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 213 (accept_3_5 35 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 94 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 213
  (Polychromatic418967fa.accept_19_14_18_4_1_4275 33 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 213 (accept_3_5 32 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 213 (accept_3_5 29 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 213 (accept_3_5 26 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 213 (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 213 (accept_3_5 23 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 213 (Polychromatic418967fa.accept_13_9_3_5_1_1605 22 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 213 (accept_3_5 20 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 213 (accept_3_5 17 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 213 (accept_3_5 14 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 213 (accept_3_5 11 94 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 213
  (Polychromatic418967fa.accept_10_9_4_3_1_539 9 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 213 (accept_3_5 8 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 94 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 213 (accept_3_5 5 94 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 213 (Polychromatic418967fa.accept_20_4_14_13_1_12582 4 94 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 94 213 (accept_3_5 2 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94
  213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 93 213 (allA_succ_of_accept 92 93 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 92 93 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 91 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 93 213 3 30 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 89 93 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 89 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 93 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 88 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 213 3 29 31 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 86 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 93 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 93 213 3 28 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 93 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 83
  93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 82 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 93 213 3 27 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 93 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 80 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 93 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 213 3 26 31 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 77 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 93 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 93 213 3 25 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 93 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 74
  93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 73 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 93 213 3 24 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 93 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 213 3 23 31 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 67 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 93 213 3 22 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 93 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 65
  93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 64 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 93 213 3 21 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 93 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 213 3 20 31 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 59 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 93 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 58 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 93 213 3 19 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 93 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 93 213 3 18 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 93 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 53 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 213 3 17 31 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 93 213 3 16 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 93 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 93 213 3 15 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 93 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 213 3 14 31 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 213 3 13 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 93 213 3 12 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 93 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 213 3 11 31 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 213 3 10 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 93 213 3 9 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 93 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 213 3 8 31 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 213 3 7 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 93 213 3 6 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 93 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 213 3 5 31 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 213
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 213 3 4 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 93 213 3 3 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 93 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 213 3 2 31 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 93 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 213 3 1 31 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 93 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 93 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 93 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 92 213 (allA_succ_of_accept 91 92 213 (accept_3_4 91 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 92 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 90 92 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 213 (accept_3_4 88 92 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 213 (Polychromatic418967fa.accept_13_9_1_5_1_964
  87 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 86 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 213 (accept_3_4 85 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 213 (accept_3_4 82 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 81 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 80 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 213 (accept_3_4 79 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 78 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 213 (accept_3_4 76 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 213 (accept_3_4 73 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 213 (accept_3_4 70 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 213 (Polychromatic418967fa.accept_13_4_1_5_1_1628 69 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 213 (accept_3_4 67 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 213 (accept_3_4 64 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 213 (Polychromatic418967fa.accept_20_3_12_13_1_3836 63 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 213 (accept_3_4 61 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 213 (accept_3_4 58 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 213
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 56 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 213 (accept_3_4 55 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 213 (accept_3_4 52 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 213 (accept_3_4 49 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 213 (accept_3_4 46 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 213 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 213 (accept_3_4 43 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 213 (accept_3_4 40 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 213
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 38 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 213 (accept_3_4 37 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 213 (Polychromatic418967fa.accept_16_4_12_5_1_2287 36 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 213 (accept_3_4 34 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 213 (accept_3_4 31 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 213 (accept_3_4 28 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 213 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 213 (accept_3_4 25 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 213 (Polychromatic418967fa.accept_16_8_12_5_1_200 24 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 213 (accept_3_4 22 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 213
  (Polychromatic418967fa.accept_15_5_2_3_1_4876 20 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 213 (accept_3_4 19 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 213 (accept_3_4 16 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 213 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 213 (accept_3_4 13 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 213 (accept_3_4 10 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 92 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 213 (accept_3_4 7 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  213 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 213 (accept_3_4 4 92 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 92 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  92 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 213 (accept_3_4 1 92 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 213
  (allA_succ_of_accept 90 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 213 (accept_3_5 89 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 213 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  87 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 213 (accept_3_5 86
  91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 213
  (Polychromatic418967fa.accept_9_4_1_6_1_284 85 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 213 (accept_3_5 83 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 213 (Polychromatic418967fa.accept_14_11_7_3_1_3416
  81 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 213 (accept_3_5 80
  91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 213
  (Polychromatic418967fa.accept_9_7_1_6_1_261 79 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 213 (accept_3_5 77 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 91 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 75
  91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 213 (accept_3_5 74 91
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 213
  (Polychromatic418967fa.accept_11_7_3_4_1_729 73 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 91 213 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 213 (accept_3_5 71 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 213 (Polychromatic418967fa.accept_21_6_7_3_1_8073
  69 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 213 (accept_3_5 68
  91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 213
  (Polychromatic418967fa.accept_9_4_1_6_1_284 67 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 213 (accept_3_5 65 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 91 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 213 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  63 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 213 (accept_3_5 62
  91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 213
  (Polychromatic418967fa.accept_9_7_1_6_1_261 61 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 91 213 (Polychromatic418967fa.accept_14_4_7_3_1_1718 60 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 213 (accept_3_5 59 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 57
  91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 213 (accept_3_5 56 91
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 213
  (Polychromatic418967fa.accept_16_7_11_5_1_4402 55 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 213 (accept_3_5 53 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 91 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 213 (Polychromatic418967fa.accept_11_7_3_4_1_729
  51 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 213 (accept_3_5 50
  91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 213
  (Polychromatic418967fa.accept_9_4_1_6_1_284 49 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 91 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 213 (accept_3_5 47 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 213
  (Polychromatic418967fa.accept_22_1_3_15_1_11046 45 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 213 (accept_3_5 44 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 213 (accept_3_5 41 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 39 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 213 (accept_3_5 38 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 213 (Polychromatic418967fa.accept_17_3_6_9_1_2761 37 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 213 (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 213 (accept_3_5 35 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 213
  (Polychromatic418967fa.accept_17_16_6_9_1_7769 33 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 213 (accept_3_5 32 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 213 (accept_3_5 29 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 213
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 213 (accept_3_5 26 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 213 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 91 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 213 (accept_3_5 23 91 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 213 (accept_3_5 20 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 213 (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 213 (accept_3_5 17 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 213
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 213 (accept_3_5 14 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 213 (accept_3_5 11 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 213
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 213 (accept_3_5 8 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  213 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 213 (accept_3_5 5 91 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 91
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 213 (accept_3_5 2 91 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 213 (Polychromatic418967fa.accept_19_1_15_4_1_4311
  1 91 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 213
  (allA_succ_of_accept 89 90 213 (Polychromatic418967fa.accept_19_13_14_4_1_5621 89 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 213 3 29 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 86 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 90 213 (Polychromatic418967fa.accept_13_7_12_5_1_1603 85 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 213 3 28 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 83
  90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 213
  (Polychromatic418967fa.accept_12_10_6_9_1_549 82 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 90 213 3 27 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 90 213 (Polychromatic418967fa.accept_12_8_6_9_1_1608 80 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 213 3 26 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 213
  (Polychromatic418967fa.accept_16_13_10_5_1_2278 77 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 76 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 213 3 25 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 74
  90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 213
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 73 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 213 3 24 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 70 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 90 213 3 23 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 213
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 68 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 213 3 22 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 65
  90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 213
  (Polychromatic418967fa.accept_11_9_2_4_1_707 64 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 90 213 3 21 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 90 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 62 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 213 (Polychromatic418967fa.accept_11_6_2_4_1_1703 61 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 213 3 20 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 90 213 3 19 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 90 213 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  56 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 213 3 18 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 52 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 90 213 3 17 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 90 213
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 50 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 213 (Polychromatic418967fa.accept_20_9_10_13_1_3835 49 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 213 3 16 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 46 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 213 3 15 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 213 3 14 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 213
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 90 213 3 13 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 38
  90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 213 3 12 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 213 3 11 30 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 213 3 10 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 213 (Polychromatic418967fa.accept_16_13_10_5_1_2278
  29 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 213
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 90 213 3 9 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 90 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 213 3 8 30 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 90 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 213 3 7 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 213 (Polychromatic418967fa.accept_11_9_2_4_1_707 20 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 90 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 213 3 6 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 213 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 213 3 5 30 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 213
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 90 213 (Polychromatic418967fa.accept_16_13_10_5_1_2278 13 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 213 3 4 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 90 213
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 90 213 3 3 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 90 213 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 213 3 2 30 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 213
  (Polychromatic418967fa.accept_20_5_10_13_1_6754 5 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 90 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 90 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 213 3 1 30 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 90 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 213
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 90 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  89 213 (allA_succ_of_accept 88 89 213 (accept_3_4 88 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 89 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 87 89 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 89 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 213 (accept_3_4 85 89 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 84
  89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 83 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 213 (accept_3_4 82 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 213 (Polychromatic418967fa.accept_13_3_11_5_1_2348 81 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 213 (accept_3_4 79 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 77 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 213 (accept_3_4 76 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 213 (accept_3_4 73 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 213 (accept_3_4 70 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 213 (Polychromatic418967fa.accept_21_6_5_3_1_12588 69 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 213 (accept_3_4 67 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 213 (accept_3_4 64 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 213 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 213 (accept_3_4 61 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 213 (accept_3_4 58 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 213 (accept_3_4 55 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 213 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 213
  (Polychromatic418967fa.accept_17_2_4_9_1_2791 53 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 213 (accept_3_4 52 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 213 (accept_3_4 49 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 213 (accept_3_4 46 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 213 (Polychromatic418967fa.accept_13_6_11_5_1_133 45 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 213 (accept_3_4 43 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 213 (Polychromatic418967fa.accept_13_3_11_5_1_2348 42 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 213 (accept_3_4 40 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 213 (accept_3_4 37 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 213
  (Polychromatic418967fa.accept_25_10_14_13_1_12587 35 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 89 213 (accept_3_4 34 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 89 213 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 89 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 213 (accept_3_4 31 89 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 30
  89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 213 (accept_3_4 28 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 213 (accept_3_4 25 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 213 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 213 (accept_3_4 22 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 213 (accept_3_4 19 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 213 (Polychromatic418967fa.accept_21_18_5_3_1_11165 18 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 213
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 213 (accept_3_4 16 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 213 (accept_3_4 13 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 213 (accept_3_4 10 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 213 (accept_3_4 7 89 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 213 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 89 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 213 (accept_3_4 4 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 89 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 213 (accept_3_4 1 89 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 213 (allA_succ_of_accept 87 88 213 (Polychromatic418967fa.accept_15_12_13_3_1_1915 87 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 213 (accept_3_5 86 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 84 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 88 213 (accept_3_5 83 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  88 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 82 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 88 213 (Polychromatic418967fa.accept_10_1_8_3_1_947 81 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 213 (accept_3_5 80 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 88 213 (accept_3_5 77 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  88 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 88 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 75 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 213 (accept_3_5 74 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 213
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 213 (accept_3_5 71 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 213 (Polychromatic418967fa.accept_15_10_13_3_1_4816 70 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 213 (accept_3_5 68 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 213 (accept_3_5 65 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 213 (Polychromatic418967fa.accept_14_7_4_3_1_488 63 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 213 (accept_3_5 62 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 213
  (Polychromatic418967fa.accept_13_8_10_5_1_977 60 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 213 (accept_3_5 59 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 213 (accept_3_5 56 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 54 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 213 (accept_3_5 53 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 213 (Polychromatic418967fa.accept_16_4_8_5_1_3317 52 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 213 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 213 (accept_3_5 50 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 88 213 (accept_3_5 47 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  88 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 88 213 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 213 (accept_3_5 44 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 213 (accept_3_5 41 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 213 (accept_3_5 38 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 213 (accept_3_5 35 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 213 (Polychromatic418967fa.accept_21_12_4_3_1_4924 33 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 213 (accept_3_5 32 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 213 (accept_3_5 29 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 213 (accept_3_5 26 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 213
  (Polychromatic418967fa.accept_15_9_13_3_1_535 24 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 213 (accept_3_5 23 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 213 (accept_3_5 20 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 213 (accept_3_5 17 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 213 (accept_3_5 14 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 213 (accept_3_5 11 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 213 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 213 (accept_3_5 8 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 213 (accept_3_5 5 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  213 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 88 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 88 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 213 (accept_3_5 2 88 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 213
  (allA_succ_of_accept 86 87 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 85 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 213 3 28 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 213
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 83 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 213 3 27 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 213 (Polychromatic418967fa.accept_13_2_9_5_1_959 80
  87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 79 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 213 3 26 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 213 (Polychromatic418967fa.accept_10_6_7_3_1_547 76 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 213 3 25 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 73 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 213 3 24 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 213 (Polychromatic418967fa.accept_11_5_10_4_1_1157
  71 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 213 3 23 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 213 (Polychromatic418967fa.accept_13_3_9_5_1_2340 68 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 67 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 213 3 22 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 213
  (Polychromatic418967fa.accept_10_5_7_3_1_561 65 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 64 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 213 3 21 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 213
  (Polychromatic418967fa.accept_12_1_3_9_1_174 61 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 213 3 20 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 213 3 19 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 213
  (Polychromatic418967fa.accept_10_6_7_3_1_547 56 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 213 3 18 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 53
  87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 213
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 52 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 213 3 17 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 213 (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 87
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 213 3 16 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 213
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 213 3 15 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 44
  87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 213 3 14 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 213 (Polychromatic418967fa.accept_13_1_9_5_1_1598 40 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 213 3 13 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 213 3 12 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 35
  87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 213 3 11 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 213 (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 213 3 10 29 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 213
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 213 (Polychromatic418967fa.accept_13_2_9_5_1_959 28 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 213 3 9 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 213
  (Polychromatic418967fa.accept_10_5_7_3_1_561 25 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 213 3 8 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 213 3 7 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 213
  (Polychromatic418967fa.accept_22_20_21_15_1_11060 20 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 87 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 87 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 213 3 6 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 17
  87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 213
  (Polychromatic418967fa.accept_10_6_7_3_1_547 16 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 213 3 5 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 213 3 4 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 213
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 213 3 3 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 213 (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 213 3 2 29 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 4 87 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 213 3 1 29 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 87 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 213
  (allA_succ_of_accept 85 86 213 (accept_3_4 85 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 213 (accept_3_4 82 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 213 (Polychromatic418967fa.accept_13_3_8_5_1_974 81 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 80 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 213 (accept_3_4 79 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 213 (accept_3_4 76 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 74 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 213 (accept_3_4 73 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 213 (Polychromatic418967fa.accept_19_15_10_4_1_9854 72 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 213 (accept_3_4 70 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 213 (accept_3_4 67 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 213 (accept_3_4 64 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 213 (accept_3_4 61 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 213 (Polychromatic418967fa.accept_21_18_2_3_1_9685 60 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 213 (accept_3_4 58 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 213 (accept_3_4 55 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 213 (accept_3_4 52 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 213 (accept_3_4 49 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 213 (accept_3_4 46 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 213 (Polychromatic418967fa.accept_30_15_26_3_1_12586 45 86 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 213 (accept_3_4 43 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 213 (accept_3_4 40 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 213 (accept_3_4 37 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 213 (accept_3_4 34 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 213
  (Polychromatic418967fa.accept_17_15_1_9_1_10058 32 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 213 (accept_3_4 31 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 213 (accept_3_4 28 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 213 (accept_3_4 25 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 213 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 213 (accept_3_4 22 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 213 (accept_3_4 19 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 213 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 213 (accept_3_4 16 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 213
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 14 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 213 (accept_3_4 13 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 213 (accept_3_4 10 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 213 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 86 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 213 (accept_3_4 7 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  213 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 213 (accept_3_4 4 86 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 213 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  86 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 213 (accept_3_4 1 86 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 213
  (allA_succ_of_accept 84 85 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 84 85 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 213 (accept_3_5 83 85 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 81
  85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 213 (accept_3_5 80 85
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 79 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 213 (Polychromatic418967fa.accept_10_8_5_3_1_543 78 85 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 213 (accept_3_5 77 85 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 75
  85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 213 (accept_3_5 74 85
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 213 (Polychromatic418967fa.accept_9_1_4_6_1_5
  73 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 213 (accept_3_5 71 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 213 (Polychromatic418967fa.accept_15_9_10_3_1_2845 69 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 213 (accept_3_5 68 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 85 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 66 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 213 (accept_3_5 65 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 213 (accept_3_5 62 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 213 (accept_3_5 59 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 57 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 213 (accept_3_5 56 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 213 (accept_3_5 53 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 213 (accept_3_5 50 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 213 (Polychromatic418967fa.accept_21_7_1_3_1_11160 49 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 213 (accept_3_5 47 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 213 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 213 (accept_3_5 44 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 213
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 213 (accept_3_5 41 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 213 (accept_3_5 38 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 213
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 213 (accept_3_5 35 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 213 (accept_3_5 32 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 213 (Polychromatic418967fa.accept_21_10_1_3_1_8092 31 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 213 (accept_3_5 29 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 213 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 213 (accept_3_5 26 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 213
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 213 (accept_3_5 23 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 213 (accept_3_5 20 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 213 (accept_3_5 17 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 213 (accept_3_5 14 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 213 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 213 (accept_3_5 11 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 213 (accept_3_5 8 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 85 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 213
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 213 (accept_3_5 5 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 85 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 213 (accept_3_5 2 85 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 85 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 213
  (allA_succ_of_accept 83 84 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 83 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 82 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 213 3 27 28 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 80 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 79 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 213 3 26 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 77
  84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 84 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 76 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 84 213 3 25 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 84 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 213 3 24 28 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 70 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 213 3 23 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 213 3 22 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84 213 3 21 28 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 84 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 84 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 213 3 20 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 58 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 84 213 3 19 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 84 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 213 3 18 28 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 213 3 17 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 50
  84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 213
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 213 3 16 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 213 3 15 28 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 213 3 14 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 41
  84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 84 213 3 13 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 84 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 213 3 12 28 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 213 3 11 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 213 3 10 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 213 3 9 28 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 213 3 8 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 84 213 3 7 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 84 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 213 3 6 28 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 213
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 213 3 5 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 213 3 4 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 213 3 3 28 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 213 3 2 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 84 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 84 213 3 1 28 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 84 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 84 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 213
  (allA_succ_of_accept 82 83 213 (accept_3_4 82 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 213 (accept_3_4 79 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 77 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 213 (accept_3_4 76 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 213 (accept_3_4 73 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 71 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 213 (accept_3_4 70 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 213 (Polychromatic418967fa.accept_15_9_8_3_1_557 69 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 213 (accept_3_4 67 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 213 (accept_3_4 64 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 213 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 213 (accept_3_4 61 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 59 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 213 (accept_3_4 58 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 213 (accept_3_4 55 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 213 (accept_3_4 52 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 213 (accept_3_4 49 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 213
  (Polychromatic418967fa.accept_25_22_8_13_1_12585 47 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 83 213 (accept_3_4 46 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 83 213 (Polychromatic418967fa.accept_18_9_11_15_1_4616 45 83 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 213 (accept_3_4 43 83 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 213 (accept_3_4 40 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 213 (accept_3_4 37 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 213 (Polychromatic418967fa.accept_20_16_3_13_1_6724 36 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 213 (accept_3_4 34 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 213 (Polychromatic418967fa.accept_19_14_7_4_1_4210 33 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 213 (accept_3_4 31 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 213
  (Polychromatic418967fa.accept_28_1_27_17_1_12584 29 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 83 213 (accept_3_4 28 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 83 213 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 83 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 213 (accept_3_4 25 83 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 213 (Polychromatic418967fa.accept_11_2_6_4_1_3028
  24 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 213 (accept_3_4 22 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 213 (accept_3_4 19 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 213 (accept_3_4 16 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 213 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 213 (accept_3_4 13 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 213 (accept_3_4 10 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 213 (accept_3_4 7 83 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 213 (accept_3_4 4 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 83 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 213 (accept_3_4 1 83 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 82 213 (allA_succ_of_accept 81 82 213 (Polychromatic418967fa.accept_10_1_2_3_1_1910 81 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 213 (accept_3_5 80 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 78 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 82 213 (accept_3_5 77 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  82 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 213 (accept_3_5 74 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 82 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 82 213 (accept_3_5 71 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  82 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 82 213 (Polychromatic418967fa.accept_19_12_6_4_1_2992 69 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 213 (accept_3_5 68 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 82 213 (accept_3_5 65 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  82 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 213 (accept_3_5 62 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 82 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 213
  (Polychromatic418967fa.accept_18_6_10_15_1_9963 60 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 82 213 (accept_3_5 59 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  82 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 82 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 213 (accept_3_5 56 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 213
  (Polychromatic418967fa.accept_11_10_5_4_1_711 54 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 82 213 (accept_3_5 53 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  82 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 213 (accept_3_5 50 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 82 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 213 (accept_3_5 47 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 213 (Polychromatic418967fa.accept_17_12_14_9_1_5079 46 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 213 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 213 (accept_3_5 44 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 213
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 213 (accept_3_5 41 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 213 (accept_3_5 38 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 213 (accept_3_5 35 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 213 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 213 (accept_3_5 32 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 213 (accept_3_5 29 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 213 (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 213 (accept_3_5 26 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 213
  (Polychromatic418967fa.accept_18_6_10_15_1_9963 24 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 213 (accept_3_5 23 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 213 (accept_3_5 20 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 213
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 213 (accept_3_5 17 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 213 (accept_3_5 14 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 213 (accept_3_5 11 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 213 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 213 (accept_3_5 8 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 213
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 213 (accept_3_5 5 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  213 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 82 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 213 (accept_3_5 2 82 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 213
  (allA_succ_of_accept 80 81 213 (Polychromatic418967fa.accept_13_2_3_5_1_2294 80 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 213 (Polychromatic418967fa.accept_13_1_3_5_1_140 79 81 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 213 3 26 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 213
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 77 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 213 3 25 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 213 (Polychromatic418967fa.accept_13_9_3_5_1_1605
  74 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 213
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 73 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 213 3 24 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 213 (Polychromatic418967fa.accept_15_10_6_3_1_1160 70 81
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 213 3 23 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 68 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 213 (Polychromatic418967fa.accept_13_2_3_5_1_2294 67 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 213 3 22 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 213 (Polychromatic418967fa.accept_15_5_6_3_1_525 65
  81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 64 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 213 3 21 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 62 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 213 (Polychromatic418967fa.accept_13_9_3_5_1_1605 61 81 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 213 3 20 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 213
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 59 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 213 (Polychromatic418967fa.accept_10_8_1_3_1_1374 58 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 213 3 19 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 213 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  56 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 213 3 18 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 213 (Polychromatic418967fa.accept_13_1_3_5_1_140 53 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 81 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 213 3 17 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 213 (Polychromatic418967fa.accept_14_7_11_3_1_5365 49 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 213 3 16 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 213 (Polychromatic418967fa.accept_13_8_3_5_1_1636
  47 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 213
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 46 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 213 3 15 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 81 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 213 3 14 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 213 (Polychromatic418967fa.accept_13_1_3_5_1_140 40 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 213 3 13 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 213 (Polychromatic418967fa.accept_10_8_1_3_1_1374
  38 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 213
  (Polychromatic418967fa.accept_13_11_3_5_1_982 37 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 213 3 12 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 213 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 81 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 213 3 11 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 213
  (Polychromatic418967fa.accept_10_2_1_3_1_233 32 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 213 (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 213 3 10 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 29
  81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 213 3 9 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 213 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 213 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 81
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 213 3 8 27 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 213
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 213 3 7 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 81 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 213
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 213 3 6 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 213 (Polychromatic418967fa.accept_18_17_9_15_1_7268 17 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 213 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 81 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 213 3 5 27 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 213
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 213 3 4 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 213 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 81 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 213
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 213 3 3 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 213 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 81 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 213 3 2 27 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 213
  (Polychromatic418967fa.accept_15_5_6_3_1_525 5 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 81 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 213 3 1 27 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 213 (Polychromatic418967fa.accept_10_2_1_3_1_233 2 81 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 81 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 213
  (allA_succ_of_accept 79 80 213 (accept_3_4 79 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 78 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 213 (accept_3_4 76 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 213 (accept_3_4 73 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 213 (Polychromatic418967fa.accept_13_7_2_5_1_2344 72 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 213 (accept_3_4 70 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 213 (Polychromatic418967fa.accept_13_4_2_5_1_4045 69 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 68 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 213 (accept_3_4 67 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 66 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 213 (accept_3_4 64 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 213 (Polychromatic418967fa.accept_14_7_10_3_1_1034 63 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 213
  (Polychromatic418967fa.accept_11_7_3_4_1_729 62 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 213 (accept_3_4 61 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 213 (Polychromatic418967fa.accept_21_18_17_3_1_4906 60 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 213 (accept_3_4 58 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 213 (accept_3_4 55 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 213 (accept_3_4 52 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 213 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 213 (accept_3_4 49 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 213 (accept_3_4 46 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 213 (Polychromatic418967fa.accept_22_1_14_15_1_12583 45 80 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 213
  (Polychromatic418967fa.accept_21_2_17_3_1_9644 44 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 213 (accept_3_4 43 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 213 (accept_3_4 40 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 213 (accept_3_4 37 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 213 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 213 (accept_3_4 34 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 213 (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 213 (accept_3_4 31 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 213 (accept_3_4 28 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 213 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 213
  (Polychromatic418967fa.accept_22_4_14_15_1_7828 26 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 213 (accept_3_4 25 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 213 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 213 (accept_3_4 22 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 213 (accept_3_4 19 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 213 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 213 (accept_3_4 16 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 213 (Polychromatic418967fa.accept_21_15_17_3_1_3373 15 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 213 (accept_3_4 13 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 213 (accept_3_4 10 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 213 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 80 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 213
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 213 (accept_3_4 7 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  213 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 80 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 213 (accept_3_4 4 80 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 80 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 80
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 213 (accept_3_4 1 80 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 213
  (allA_succ_of_accept 78 79 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 213 (accept_3_5 77 79 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 75
  79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 213 (accept_3_5 74 79
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 213 (Polychromatic418967fa.accept_9_1_7_6_1_75
  73 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 213
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 72 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 213 (accept_3_5 71 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 213 (accept_3_5 68 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 67 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 213 (accept_3_5 65 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 213 (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 213 (accept_3_5 62 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 213
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 60 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 213 (accept_3_5 59 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 213 (accept_3_5 56 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 213 (accept_3_5 53 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 213 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 213 (accept_3_5 50 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 213 (accept_3_5 47 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 213 (Polychromatic418967fa.accept_13_6_1_5_1_3988 45 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 213 (accept_3_5 44 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 213 (accept_3_5 41 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 213 (accept_3_5 38 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 213 (accept_3_5 35 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 213 (accept_3_5 32 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 213 (accept_3_5 29 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 213 (accept_3_5 26 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 213 (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 213
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 213 (accept_3_5 23 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 213 (accept_3_5 20 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 213 (accept_3_5 17 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 213 (accept_3_5 14 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 213 (accept_3_5 11 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 213 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 213 (accept_3_5 8 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 213 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 79 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 213 (accept_3_5 5 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 79 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 213 (accept_3_5 2 79 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 79 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 213
  (allA_succ_of_accept 77 78 213 (Polychromatic418967fa.accept_18_5_6_15_1_3413 77 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 76 78 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 213 3 25 26 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 213 (Polychromatic418967fa.accept_16_9_14_5_1_2239 73 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 213 3 24 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 213
  (Polychromatic418967fa.accept_12_10_6_9_1_549 70 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 213 3 23 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 213 3 22 26 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 64 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 213 3 21 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 62
  78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 213 3 20 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 78 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 213 3 19 26 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 213
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 213 3 18 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 53
  78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 213
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 52 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 213 3 17 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 213 (Polychromatic418967fa.accept_19_11_2_4_1_8443 49 78
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 213 3 16 26 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 213 3 15 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 213 3 14 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 213 (Polychromatic418967fa.accept_10_1_8_3_1_947 41 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 78 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 213 3 13 26 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 213
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 213 3 12 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 213
  (Polychromatic418967fa.accept_12_10_6_9_1_549 34 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 213 3 11 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 213 3 10 26 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 213
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 29 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 213 3 9 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 78 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 213 3 8 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 78 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 213 3 7 26 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 213
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 213 3 6 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 213 (Polychromatic418967fa.accept_18_17_6_15_1_8704 17 78
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 213 3 5 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 213 (Polychromatic418967fa.accept_17_13_10_9_1_946 13 78
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 213 3 4 26 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 213 3 3 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 213 (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 78 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 213 3 2 26 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 78 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 213 3 1 26 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 78 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 213 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 78 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 213
  (allA_succ_of_accept 76 77 213 (accept_3_4 76 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 75 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 213 (accept_3_4 73 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 213 (Polychromatic418967fa.accept_13_7_12_5_1_1603 72 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 71 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 213 (accept_3_4 70 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 213 (Polychromatic418967fa.accept_13_4_12_5_1_476 69 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 213 (accept_3_4 67 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 65 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 213 (accept_3_4 64 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 213 (accept_3_4 61 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 213 (Polychromatic418967fa.accept_13_8_12_5_1_1604 60 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 213
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 59 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 213 (accept_3_4 58 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 213 (accept_3_4 55 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 53 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 213 (accept_3_4 52 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 213 (accept_3_4 49 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 213 (accept_3_4 46 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 213 (accept_3_4 43 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 213 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 213
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 213 (accept_3_4 40 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 213 (accept_3_4 37 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 213 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 213 (accept_3_4 34 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 213 (Polychromatic418967fa.accept_13_7_12_5_1_1603 33 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 213 (accept_3_4 31 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 213 (accept_3_4 28 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 213 (accept_3_4 25 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 213
  (Polychromatic418967fa.accept_21_2_14_3_1_4933 23 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 213 (accept_3_4 22 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 213 (accept_3_4 19 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 213 (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 213 (accept_3_4 16 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 213 (accept_3_4 13 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 213 (accept_3_4 10 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 213 (Polychromatic418967fa.accept_16_9_13_5_1_2238 9 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 213 (accept_3_4 7 77 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 213 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 77 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 213
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 213 (accept_3_4 4 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 77 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 213 (accept_3_4 1 77 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 213 (allA_succ_of_accept 75 76 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 75 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 213 (accept_3_5 74 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 213 (accept_3_5 71 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 213 (Polychromatic418967fa.accept_10_9_6_3_1_545 69 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 213 (accept_3_5 68 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 66 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 213 (accept_3_5 65 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 213 (Polychromatic418967fa.accept_18_9_4_15_1_555 63 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 213 (accept_3_5 62 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 213 (accept_3_5 59 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 213 (accept_3_5 56 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 54 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 213 (accept_3_5 53 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 213 (accept_3_5 50 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 213 (accept_3_5 47 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 213 (Polychromatic418967fa.accept_13_6_11_5_1_133 45 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 213 (accept_3_5 44 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 213 (accept_3_5 41 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 213 (Polychromatic418967fa.accept_16_8_12_5_1_200 40 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 213 (accept_3_5 38 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 213
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 213 (accept_3_5 35 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 213 (accept_3_5 32 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 213 (accept_3_5 29 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 213 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 213 (accept_3_5 26 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 213
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 213 (accept_3_5 23 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 213 (Polychromatic418967fa.accept_23_22_7_6_1_5838 22 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 213 (accept_3_5 20 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 213 (accept_3_5 17 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 213 (Polychromatic418967fa.accept_30_15_16_3_1_3855 15 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 213 (accept_3_5 14 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 213 (accept_3_5 11 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 213 (accept_3_5 8 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 213 (accept_3_5 5 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  213 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 76 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 76 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 76 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 213 (accept_3_5 2 76 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 76 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 213 (allA_succ_of_accept
  74 75 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 75 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 213 3 24 25 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 213 3 23 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 68
  75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 213 3 22 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 213 3 21 25 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 213 3 20 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 213 3 19 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 213 3 18 25 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 213 3 17 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 213 3 16 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 213 3 15 25 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 213 3 14 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 213 3 13 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 213 3 12 25 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 213 3 11 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 213 3 10 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 213 3 9 25 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 213 3 8 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 213 3 7 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 213 3 6 25 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 213 3 5 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 213 3 4 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 213 3 3 25 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 213 3 2 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 75 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 213 3 1 25 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 75 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 213 (allA_succ_of_accept
  73 74 213 (accept_3_4 73 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 213
  (Polychromatic418967fa.accept_22_6_8_15_1_6038 72 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 213 (accept_3_4 70 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 213 (Polychromatic418967fa.accept_9_5_2_6_1_265 68
  74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 213 (accept_3_4 67 74
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 213
  (Polychromatic418967fa.accept_9_3_2_6_1_264 66 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 213 (accept_3_4 64 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 62
  74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 213 (accept_3_4 61 74
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 213
  (Polychromatic418967fa.accept_16_12_10_5_1_5457 60 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 213 (accept_3_4 58 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 213 (Polychromatic418967fa.accept_11_1_8_4_1_717
  56 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 74 213 (accept_3_4 55
  74 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 74 213
  (Polychromatic418967fa.accept_12_6_2_9_1_537 54 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 74 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 213 (accept_3_4 52 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 50
  74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 74 213 (accept_3_4 49 74
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 74 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 213 (accept_3_4 46 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 74 213 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 213 (Polychromatic418967fa.accept_9_8_2_6_1_875 44
  74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 74 213 (accept_3_4 43 74
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 74 213
  (Polychromatic418967fa.accept_12_6_2_9_1_537 42 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 74 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 213 (accept_3_4 40 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 213
  (Polychromatic418967fa.accept_27_11_20_24_1_6652 38 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 74 213 (accept_3_4 37 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 74 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 213 (accept_3_4 34 74 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 213 (Polychromatic418967fa.accept_17_16_6_9_1_7769
  33 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 213 (accept_3_4 31 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 213 (accept_3_4 28 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 213 (accept_3_4 25 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 213 (Polychromatic418967fa.accept_20_4_14_13_1_12582 24 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 213 (accept_3_4 22 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 74 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 213 (accept_3_4 19 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 213 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 213 (accept_3_4 16 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 213 (accept_3_4 13 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 213 (accept_3_4 10 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 213 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 74 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 213 (accept_3_4 7 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  213 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 213 (accept_3_4 4 74 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 213 (Polychromatic418967fa.accept_13_2_9_5_1_959 2
  74 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 213 (accept_3_4 1 74 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 213 (allA_succ_of_accept
  72 73 213 (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 213 (accept_3_5 71 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 73 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 213 (Polychromatic418967fa.accept_11_3_7_4_1_1133 69 73 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 213 (accept_3_5 68 73 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 67
  73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 213 (accept_3_5 65 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 213 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 213 (accept_3_5 62 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 61 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 213 (accept_3_5 59 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 213 (accept_3_5 56 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 213 (Polychromatic418967fa.accept_13_3_8_5_1_974 55 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 213
  (Polychromatic418967fa.accept_15_9_13_3_1_535 54 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 213 (accept_3_5 53 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 51 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 213 (accept_3_5 50 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 213 (accept_3_5 47 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 213 (Polychromatic418967fa.accept_16_13_9_5_1_3302 45 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 213 (accept_3_5 44 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 73 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 213
  (Polychromatic418967fa.accept_13_3_8_5_1_974 42 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 213 (accept_3_5 41 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 213 (accept_3_5 38 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 213 (Polychromatic418967fa.accept_21_16_10_3_1_9671 37 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 213 (accept_3_5 35 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 213 (Polychromatic418967fa.accept_16_1_9_5_1_5443 33 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 213 (accept_3_5 32 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 213 (accept_3_5 29 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 213 (accept_3_5 26 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 213
  (Polychromatic418967fa.accept_15_9_13_3_1_535 24 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 213 (accept_3_5 23 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 213 (accept_3_5 20 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 213 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 213
  (Polychromatic418967fa.accept_21_18_10_3_1_9672 18 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 213 (accept_3_5 17 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 213 (accept_3_5 14 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 213 (accept_3_5 11 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 213 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 213 (accept_3_5 8 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 73 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 213
  (Polychromatic418967fa.accept_40_6_33_13_1_12581 6 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 213 (accept_3_5 5 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 73 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 213 (accept_3_5 2 73 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 213 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1 73 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 213 (allA_succ_of_accept 71
  72 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 213 (Polychromatic418967fa.accept_17_2_4_9_1_2791 70 72 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 213 3 23 24 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 213 (Polychromatic418967fa.accept_13_2_7_5_1_3189 67 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 213 3 22 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 213 (Polychromatic418967fa.accept_10_5_2_3_1_239 65
  72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 64 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 213 3 21 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 72 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 213 3 20 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 213
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 59 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 213 (Polychromatic418967fa.accept_15_13_12_3_1_1180 58 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 213 3 19 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 213 (Polychromatic418967fa.accept_19_18_15_4_1_9838
  56 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 213 3 18 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 213 (Polychromatic418967fa.accept_15_8_12_3_1_1912 53 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 213 (Polychromatic418967fa.accept_15_7_12_3_1_1137 52 72
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 213 3 17 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 213 (Polychromatic418967fa.accept_19_11_15_4_1_7010 49 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 213 3 16 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 213
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 46 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 213 3 15 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 213 (Polychromatic418967fa.accept_16_12_8_5_1_3316 44 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 213 3 14 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 213 3 13 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 213 (Polychromatic418967fa.accept_13_12_7_5_1_3147
  38 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 213
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 213 3 12 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 213 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 72 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 213 3 11 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 213
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 213 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 213 3 10 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 213
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 28 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 213 3 9 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 213 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 72 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 213 3 8 24 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 213
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 213 3 7 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 72 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 213 3 6 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 213 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 213 (Polychromatic418967fa.accept_21_16_9_3_1_6436 16 72
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 213 3 5 24 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 213
  (Polychromatic418967fa.accept_17_14_4_9_1_2792 14 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 213 3 4 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 213 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 72 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 213
  (Polychromatic418967fa.accept_19_10_15_4_1_1852 10 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 213 3 3 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 213 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 72 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 213 3 2 24 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 213 (Polychromatic418967fa.accept_16_4_8_5_1_3317 4 72 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 213 3 1 24 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 213 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 72 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 213
  (allA_succ_of_accept 70 71 213 (accept_3_4 70 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 213 (Polychromatic418967fa.accept_13_4_6_5_1_2333 69 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 213 (accept_3_4 67 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 213 (accept_3_4 64 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 213 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 213 (accept_3_4 61 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 213 (accept_3_4 58 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 213 (accept_3_4 55 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 213 (accept_3_4 52 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 213 (accept_3_4 49 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 213 (accept_3_4 46 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 213 (Polychromatic418967fa.accept_17_11_3_9_1_6387 45 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 213 (accept_3_4 43 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 213 (accept_3_4 40 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 213 (accept_3_4 37 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 213 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 213
  (Polychromatic418967fa.accept_17_1_3_9_1_958 35 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 213 (accept_3_4 34 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 213 (accept_3_4 31 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 213 (accept_3_4 28 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 213 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 213 (accept_3_4 25 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 213 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 213 (accept_3_4 22 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 213 (accept_3_4 19 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 213
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 213 (accept_3_4 16 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 213 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 213 (accept_3_4 13 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 213 (accept_3_4 10 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 213 (accept_3_4 7 71 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 213 (accept_3_4 4 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 71 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 213 (accept_3_4 1 71 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 213
  (allA_succ_of_accept 69 70 213 (Polychromatic418967fa.accept_15_9_10_3_1_2845 69 70 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 213 (accept_3_5 68 70 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 70 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 66
  70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 70 213 (accept_3_5 65 70
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 70 213 (Polychromatic418967fa.accept_9_1_7_6_1_75
  64 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 70 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 70 213 (accept_3_5 62 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  70 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 70 213 (Polychromatic418967fa.accept_18_6_16_15_1_7287 60 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 213 (accept_3_5 59 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 70 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 213 (accept_3_5 56 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  70 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 70 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 213 (accept_3_5 53 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 213 (Polychromatic418967fa.accept_15_7_10_3_1_2891 52 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 213 (accept_3_5 50 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  70 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 70 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 213 (accept_3_5 47 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 70 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 213
  (Polychromatic418967fa.accept_17_11_2_9_1_6358 45 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 70 213 (accept_3_5 44 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  70 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 70 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 70 213 (accept_3_5 41 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 70 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 70 213 (accept_3_5 38 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  70 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 70 213 (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 70 213 (accept_3_5 35 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 70 213 (Polychromatic418967fa.accept_19_15_13_4_1_7033 34 70
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 70 213
  (Polychromatic418967fa.accept_16_1_6_5_1_4385 33 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 70 213 (accept_3_5 32 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  70 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 70 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 213 (accept_3_5 29 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 213 (accept_3_5 26 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 213 (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 213 (accept_3_5 23 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 70 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 70 213 (accept_3_5 20 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  70 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 70 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 213 (accept_3_5 17 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 70 213 (Polychromatic418967fa.accept_21_16_7_3_1_8093 16 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 70 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 70 213 (accept_3_5 14 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  70 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 70 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 70 213 (accept_3_5 11 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 70 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 70 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 213
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 213 (accept_3_5 8 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 70 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 213 (accept_3_5 5 70 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 70 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 70 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 213 (accept_3_5 2 70 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 213 (allA_succ_of_accept 68 69
  213 (Polychromatic418967fa.accept_15_8_9_3_1_1194 68 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 69 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 69 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 213 3 22 23 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 213 (Polychromatic418967fa.accept_10_4_9_3_1_1907 64 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 213 3 21 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 213 (Polychromatic418967fa.accept_11_7_3_4_1_729 62
  69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 213
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 61 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 213 3 20 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 213 (Polychromatic418967fa.accept_17_8_1_9_1_7738 59 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 69 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 213 3 19 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 213
  (Polychromatic418967fa.accept_10_6_9_3_1_935 56 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 213 (Polychromatic418967fa.accept_15_10_9_3_1_1947 55 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 213 3 18 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 53
  69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 213
  (Polychromatic418967fa.accept_14_10_13_3_1_2552 52 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 213 3 17 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 213 (Polychromatic418967fa.accept_15_5_9_3_1_528 50 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 213 (Polychromatic418967fa.accept_13_10_4_5_1_2331 49 69
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 213 3 16 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 213
  (Polychromatic418967fa.accept_21_5_6_3_1_12580 47 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 213 3 15 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 44
  69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 213
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 213 3 14 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 213 (Polychromatic418967fa.accept_13_2_4_5_1_3152 41 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 213 (Polychromatic418967fa.accept_11_7_3_4_1_729 40 69 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 213 3 13 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 213
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 38 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 213 3 12 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 213 (Polychromatic418967fa.accept_13_9_4_5_1_1651
  35 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 213
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 34 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 213 3 11 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 213 (Polychromatic418967fa.accept_22_9_3_15_1_4527 31 69
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 213 3 10 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 213
  (Polychromatic418967fa.accept_11_7_3_4_1_729 29 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 213 (Polychromatic418967fa.accept_13_2_4_5_1_3152 28 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 213 3 9 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 213 (Polychromatic418967fa.accept_10_6_9_3_1_935 26 69 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 213 3 8 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 213 (Polychromatic418967fa.accept_13_9_4_5_1_1651 22 69 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 213 3 7 23 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 213
  (Polychromatic418967fa.accept_15_5_9_3_1_528 20 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 213 (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 213 3 6 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 213 (Polychromatic418967fa.accept_25_17_19_13_1_12579 17 69
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 213 3 5 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 213 (Polychromatic418967fa.accept_10_4_9_3_1_1907 14 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 213 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 69
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 213 3 4 23 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 213 (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 213 3 3 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 213 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 69 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 213
  (Polychromatic418967fa.accept_11_7_3_4_1_729 7 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 213 3 2 23 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 213 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 69 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 213 3 1 23 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 69 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 213 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 69 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 213 (allA_succ_of_accept 67 68 213 (accept_3_4 67 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 68 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 68 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 213 (accept_3_4 64 68 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 213 (Polychromatic418967fa.accept_13_11_3_5_1_982
  63 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 62 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 213 (accept_3_4 61 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 213 (Polychromatic418967fa.accept_13_8_3_5_1_1636 60 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 213 (accept_3_4 58 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 68 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 213 (accept_3_4 55 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 213 (accept_3_4 52 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 68 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 213 (accept_3_4 49 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 213 (accept_3_4 46 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 213 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 68 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 213 (accept_3_4 43 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 213 (Polychromatic418967fa.accept_11_9_2_4_1_707 42 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 213 (accept_3_4 40 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 68 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 213 (accept_3_4 37 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 213 (accept_3_4 34 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 68 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 213
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 32 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 213 (accept_3_4 31 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 213 (accept_3_4 28 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 213 (Polychromatic418967fa.accept_13_1_3_5_1_140 27 68 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 213 (accept_3_4 25 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 213 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 213 (accept_3_4 22 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 68 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 213 (accept_3_4 19 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 213 (accept_3_4 16 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 68 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 213
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 213 (accept_3_4 13 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 213 (accept_3_4 10 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 68 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 213 (accept_3_4 7 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  213 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 68 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 213 (accept_3_4 4 68 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 68 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 68
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 213 (accept_3_4 1 68 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 213 (allA_succ_of_accept 66 67
  213 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 213 (accept_3_5 65 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 213 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 213 (accept_3_5 62 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 67 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 213
  (Polychromatic418967fa.accept_21_18_4_3_1_8082 60 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 213 (accept_3_5 59 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 213 (accept_3_5 56 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 67 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 213 (accept_3_5 53 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 213 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 213 (accept_3_5 50 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 213 (Polychromatic418967fa.accept_13_10_2_5_1_1633 49 67 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 213 (accept_3_5 47 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 213 (accept_3_5 44 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 67 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 213 (accept_3_5 41 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 213 (accept_3_5 38 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 67 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 213 (accept_3_5 35 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 213 (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 213 (accept_3_5 32 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 213 (Polychromatic418967fa.accept_22_9_1_15_1_9461 31 67 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 213 (accept_3_5 29 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 213 (accept_3_5 26 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 67 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 213
  (Polychromatic418967fa.accept_10_4_7_3_1_54 24 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 213 (accept_3_5 23 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 213 (accept_3_5 20 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 67 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 213 (accept_3_5 17 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 213 (accept_3_5 14 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 67 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 213 (accept_3_5 11 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 213 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 213 (accept_3_5 8 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 67 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 213 (accept_3_5 5 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 67 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 213 (accept_3_5 2 67 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 67 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 213 (allA_succ_of_accept 65 66
  213 (Polychromatic418967fa.accept_9_2_3_6_1_88 65 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 213 3 21 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 62
  66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 213 3 20 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 58 66 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 213 3 19 22 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 213
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 213 3 18 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 213 3 17 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 66 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 213 3 16 22 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 213 3 15 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 213 3 14 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 66 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 213 3 13 22 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 213
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 213 3 12 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 213 3 11 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 213 3 10 22 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 213
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 213 3 9 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 66 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 213 3 8 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 66 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 213 3 7 22 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 213
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 213 3 6 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 66 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 213 3 5 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 66 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 213 3 4 22 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 213 3 3 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 66 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 213 3 2 22 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 66 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 213 3 1 22 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 213
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 66 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 66 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 213 (allA_succ_of_accept 64 65 213 (accept_3_4 64 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 65 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 65 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 213 (accept_3_4 61 65 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 60
  65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 59 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 213 (accept_3_4 58 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 213 (accept_3_4 55 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 65 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 213 (accept_3_4 52 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 213 (accept_3_4 49 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 65 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 213 (accept_3_4 46 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 213 (Polychromatic418967fa.accept_16_13_1_5_1_5469 45 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 213 (accept_3_4 43 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 213 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 65 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 213 (accept_3_4 40 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 213 (accept_3_4 37 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 65 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 213 (accept_3_4 34 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 213 (accept_3_4 31 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 65 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 213 (accept_3_4 28 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 213 (accept_3_4 25 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 213 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 65 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 213 (accept_3_4 22 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 213 (accept_3_4 19 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 213 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 65 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 213 (accept_3_4 16 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 213 (accept_3_4 13 65 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 213
  (Polychromatic418967fa.accept_22_11_21_15_1_7853 11 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 65 213 (accept_3_4 10 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 65 213 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 65 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 213 (accept_3_4 7 65 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 213 (accept_3_4 4 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 65 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 213 (accept_3_4 1 65 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 213
  (allA_succ_of_accept 63 64 213 (Polychromatic418967fa.accept_18_9_10_15_1_7254 63 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 213 (accept_3_5 62 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 60
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 213 (accept_3_5 59 64
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 58 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 64 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 213 (accept_3_5 56 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 64 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 54
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 213 (accept_3_5 53 64
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 213
  (Polychromatic418967fa.accept_9_7_1_6_1_261 52 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 64 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 213 (accept_3_5 50 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 64 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 48
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 213 (accept_3_5 47 64
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 46 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 64 213 (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 213 (accept_3_5 44 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 64 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 213 (Polychromatic418967fa.accept_12_6_4_9_1_544
  42 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 213 (accept_3_5 41
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 40 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 64 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 213 (accept_3_5 38 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 64 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 213 (Polychromatic418967fa.accept_21_15_1_3_1_9587
  36 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 213 (accept_3_5 35
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 213
  (Polychromatic418967fa.accept_9_7_1_6_1_261 34 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 64 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 213 (accept_3_5 32 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 64 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 30
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 213 (accept_3_5 29 64
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 213
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 28 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 64 213 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 213 (accept_3_5 26 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 64 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 213 (Polychromatic418967fa.accept_11_2_9_4_1_310
  24 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 213 (accept_3_5 23
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 213
  (Polychromatic418967fa.accept_9_4_1_6_1_284 22 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 64 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 213 (accept_3_5 20 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 64 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 18
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 213 (accept_3_5 17 64
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 64 213 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 213 (accept_3_5 14 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 64 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 12
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 213 (accept_3_5 11 64
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 213
  (Polychromatic418967fa.accept_17_10_13_9_1_3913 10 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 64 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 213 (accept_3_5 8 64 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 64 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 213 (Polychromatic418967fa.accept_12_6_4_9_1_544 6
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 213 (accept_3_5 5 64 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4
  64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 213 (accept_3_5 2 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 213
  (allA_succ_of_accept 62 63 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 63 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 213 3 20 21 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 213
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 63 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 213 3 19 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 63 213 (Polychromatic418967fa.accept_11_1_8_4_1_717 56
  63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 55 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 63 213 3 18 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 63 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 213 (Polychromatic418967fa.accept_14_10_7_3_1_1022 52 63
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 213 3 17 21 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 213 3 16 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  47 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 63 213 3 15 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 213 (Polychromatic418967fa.accept_20_4_3_13_1_8257 44 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 63 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 213 3 14 21 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 213
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 213 (Polychromatic418967fa.accept_11_7_8_4_1_718 40 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 213 3 13 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 213
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 213 3 12 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 63 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 213 3 11 21 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 213
  (Polychromatic418967fa.accept_13_6_11_5_1_133 32 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 213 3 10 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 213 (Polychromatic418967fa.accept_11_7_8_4_1_718 29
  63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 213
  (Polychromatic418967fa.accept_18_10_9_15_1_7267 28 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 63 213 3 9 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 63 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 213 3 8 21 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 213
  (Polychromatic418967fa.accept_11_1_8_4_1_717 23 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 213 3 7 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 213 (Polychromatic418967fa.accept_13_7_11_5_1_2302 20 63 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 213 3 6 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 213 (Polychromatic418967fa.accept_13_3_11_5_1_2348 16 63
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 213 3 5 21 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 213 3 4 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 213 3 3 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 213 (Polychromatic418967fa.accept_20_8_3_13_1_2590 8 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 213 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 63 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 213 3 2 21 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 213
  (Polychromatic418967fa.accept_12_5_3_9_1_541 5 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 213 (Polychromatic418967fa.accept_14_4_7_3_1_1718 4 63 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 213 3 1 21 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 213
  (Polychromatic418967fa.accept_11_1_8_4_1_717 1 63 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 213 (allA_succ_of_accept
  61 62 213 (accept_3_4 61 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 213 (accept_3_4 58 62 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 56
  62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 213 (accept_3_4 55 62
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 213
  (Polychromatic418967fa.accept_12_6_2_9_1_537 54 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 62 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 213 (accept_3_4 52 62 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 213 (Polychromatic418967fa.accept_9_5_8_6_1_281 50
  62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 213 (accept_3_4 49 62
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 213 (Polychromatic418967fa.accept_9_3_8_6_1_80
  48 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 62 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 62 213 (accept_3_4 46 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  62 213 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 62 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 213 (accept_3_4 43 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 62 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 62 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 62 213 (accept_3_4 40 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  62 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 62 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 213 (accept_3_4 37 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 213 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 62 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 62 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 62 213 (accept_3_4 34 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  62 213 (Polychromatic418967fa.accept_21_12_20_3_1_12578 33 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 62 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 213 (accept_3_4 31 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 62 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 62 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 62 213 (accept_3_4 28 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  62 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 62 213 (Polychromatic418967fa.accept_16_10_14_5_1_5496 26 62 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 62 213 (accept_3_4 25 62 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 62 213 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 62
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 62 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 62 213 (accept_3_4 22 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  62 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 62 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 62 213 (accept_3_4 19 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 62 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 62 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 62 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 62 213 (accept_3_4 16 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  62 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 62 213 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 62 213 (accept_3_4 13 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 62 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 62 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 62 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 62 213 (accept_3_4 10 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  62 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 62 213 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 62 213 (accept_3_4 7 62 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 62 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 62 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 62 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 62 213 (accept_3_4 4 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 62
  213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 62 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 62 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 213 (accept_3_4 1 62 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 62 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 213
  (allA_succ_of_accept 60 61 213 (Polychromatic418967fa.accept_21_18_19_3_1_9649 60 61 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 61 213 (accept_3_5 59 61 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 61 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 61 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 57
  61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 213 (accept_3_5 56 61
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 213 (Polychromatic418967fa.accept_9_1_7_6_1_75
  55 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 213
  (Polychromatic418967fa.accept_13_2_9_5_1_959 54 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 213 (accept_3_5 53 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 213 (accept_3_5 50 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 61 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 213 (accept_3_5 47 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 213 (Polychromatic418967fa.accept_27_18_7_24_1_12577 45 61 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 213 (accept_3_5 44 61 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 61 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 213
  (Polychromatic418967fa.accept_10_2_1_3_1_233 42 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 213 (accept_3_5 41 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 213 (accept_3_5 38 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 213 (accept_3_5 35 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 213 (Polychromatic418967fa.accept_16_1_13_5_1_2280 33 61 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 213 (accept_3_5 32 61 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 61 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 213 (accept_3_5 29 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 213 (accept_3_5 26 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 213 (Polychromatic418967fa.accept_16_9_13_5_1_2238 25 61 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 213
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 213 (accept_3_5 23 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 213 (accept_3_5 20 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 61 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 213
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 213 (accept_3_5 17 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 213 (accept_3_5 14 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 61 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 213 (accept_3_5 11 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 213 (accept_3_5 8 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 213 (Polychromatic418967fa.accept_24_7_13_21_1_10971 7 61 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 213
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 213 (accept_3_5 5 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 61 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 213 (accept_3_5 2 61 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 213 (allA_succ_of_accept 59 60 213 (Polychromatic418967fa.accept_18_5_6_15_1_3413 59 60 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 213
  (Polychromatic418967fa.accept_16_10_12_5_1_2254 58 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 213 3 19 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 213 (Polychromatic418967fa.accept_16_8_12_5_1_200 56 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 60 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 213 3 18 20 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 213
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 53 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 213 (Polychromatic418967fa.accept_16_4_12_5_1_2287 52 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 213 3 17 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 50
  60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 213
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 213 3 16 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 213 (Polychromatic418967fa.accept_18_11_6_15_1_5953 47 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 213 (Polychromatic418967fa.accept_18_10_6_15_1_3412 46 60
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 213 3 15 20 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 213
  (Polychromatic418967fa.accept_19_6_3_4_1_7040 44 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 213 3 14 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 213
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 40 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 60 213 3 13 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 213 (Polychromatic418967fa.accept_13_12_8_5_1_976 38 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 213 (Polychromatic418967fa.accept_19_18_3_4_1_7079 37 60
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 213 3 12 20 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 213
  (Polychromatic418967fa.accept_14_7_4_3_1_488 35 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 213 3 11 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 213 (Polychromatic418967fa.accept_11_10_5_4_1_711
  32 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 213
  (Polychromatic418967fa.accept_21_10_18_3_1_11147 31 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 60 213 3 10 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 60 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 213
  (Polychromatic418967fa.accept_18_10_6_15_1_3412 28 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 60 213 3 9 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 60 213 (Polychromatic418967fa.accept_16_10_12_5_1_2254 26 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 60 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 213 3 8 20 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 213
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 60 213 3 7 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 60 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 60 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 213
  (Polychromatic418967fa.accept_21_19_18_3_1_4910 19 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 213 3 6 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 60 213 (Polychromatic418967fa.accept_13_3_8_5_1_974 16 60 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 213 3 5 20 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 213
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 14 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 60 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 213 3 4 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 213 (Polychromatic418967fa.accept_18_11_6_15_1_5953 11 60
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 213
  (Polychromatic418967fa.accept_11_10_5_4_1_711 10 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 60 213 3 3 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 60 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 60 213 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 60 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 213 3 2 20 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 213
  (Polychromatic418967fa.accept_18_5_6_15_1_3413 5 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 60 213 (Polychromatic418967fa.accept_16_4_12_5_1_2287 4 60 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 60 213 3 1 20 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 60 213 (Polychromatic418967fa.accept_21_2_18_3_1_9697 2 60 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 213 (allA_succ_of_accept 58
  59 213 (accept_3_4 58 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 213
  (Polychromatic418967fa.accept_9_3_5_6_1_253 57 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 213 (accept_3_4 55 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 213 (Polychromatic418967fa.accept_9_8_5_6_1_538 53
  59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 213 (accept_3_4 52 59
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 213
  (Polychromatic418967fa.accept_12_3_11_9_1_193 51 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 213 (accept_3_4 49 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 59 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 213 (Polychromatic418967fa.accept_9_2_5_6_1_536 47
  59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 213 (accept_3_4 46 59
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 213
  (Polychromatic418967fa.accept_17_11_8_9_1_8919 45 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 59 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 213 (accept_3_4 43 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 59 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 213 (Polychromatic418967fa.accept_13_2_7_5_1_3189
  41 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 213 (accept_3_4 40
  59 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 213
  (Polychromatic418967fa.accept_9_3_5_6_1_253 39 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 59 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 213 (accept_3_4 37 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 59 213 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 59 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 213 (Polychromatic418967fa.accept_9_8_5_6_1_538 35
  59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 213 (accept_3_4 34 59
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 213
  (Polychromatic418967fa.accept_17_16_8_9_1_1772 33 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 59 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 213 (accept_3_4 31 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 59 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 213 (Polychromatic418967fa.accept_9_2_5_6_1_536 29
  59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 213 (accept_3_4 28 59
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 213
  (Polychromatic418967fa.accept_12_3_11_9_1_193 27 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 59 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 213 (accept_3_4 25 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 59 213 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 59 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 213 (Polychromatic418967fa.accept_16_7_11_5_1_4402
  23 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 213 (accept_3_4 22
  59 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 213
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 59 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 213 (accept_3_4 19 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 59 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 213 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 213 (accept_3_4 16 59
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 213
  (Polychromatic418967fa.accept_12_3_11_9_1_193 15 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 59 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 213 (accept_3_4 13 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 59 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 59 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 213 (Polychromatic418967fa.accept_9_2_5_6_1_536 11
  59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 213 (accept_3_4 10 59
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 213
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 213 (accept_3_4 7 59 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 213 (Polychromatic418967fa.accept_19_5_2_4_1_9840 5
  59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 213 (accept_3_4 4 59 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 213 (accept_3_4 1 59 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 213 (allA_succ_of_accept 57 58 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 58 213 (accept_3_5 56 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  58 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 58 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 213 (accept_3_5 53 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 58 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 58 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 58 213 (accept_3_5 50 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  58 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 58 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 58 213 (accept_3_5 47 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 58 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 58 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 58 213
  (Polychromatic418967fa.accept_10_5_8_3_1_229 45 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 58 213 (accept_3_5 44 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  58 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 58 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 58 213 (accept_3_5 41 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 58 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 58 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 58 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 58 213 (accept_3_5 38 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  58 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 58 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 58 213 (accept_3_5 35 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 58 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 58 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 58 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 58 213 (accept_3_5 32 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  58 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 58 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 58 213 (accept_3_5 29 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 58 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 58 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 58 213 (accept_3_5 26 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  58 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 58 213 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 58 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 58 213 (accept_3_5 23 58 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 58 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 58 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 58 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 58 213 (accept_3_5 20 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  58 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 58 213 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 58 213 (accept_3_5 17 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 58 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 58 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 58 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 58 213 (accept_3_5 14 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  58 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 58 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 58 213 (accept_3_5 11 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 58 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 58 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 213
  (Polychromatic418967fa.accept_15_9_13_3_1_535 9 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 58 213 (accept_3_5 8 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58
  213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 58 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 58 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 58 213 (accept_3_5 5 58 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 58 213 (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 58 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 58 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 213 (accept_3_5 2 58 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 213 (allA_succ_of_accept 56 57 213
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 213 3 18 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 53
  57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 52 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 213 3 17 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 49 57 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 213 3 16 19 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 213 3 15 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 213 3 14 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 57 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 213 3 13 19 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 213
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 213 3 12 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 213 3 11 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 57 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 213 3 10 19 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 213
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 213 3 9 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 57 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 213 3 8 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 57 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 213 3 7 19 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 213 3 6 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 57 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 213 3 5 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 57 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 213 3 4 19 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 57 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 213 3 3 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 57 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 57 213 3 2 19 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 57 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 213 3 1 19 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 57 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 57 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 57 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 57 213))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  56 213 (allA_succ_of_accept 55 56 213 (accept_3_4 55 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 56 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 56 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 56 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 213 (accept_3_4 52 56 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 56 213 (Polychromatic418967fa.accept_13_12_4_5_1_1637
  51 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 50 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 56 213 (accept_3_4 49 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  56 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 56 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 213 (accept_3_4 46 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 56 213 (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 56 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 213 (accept_3_4 43 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 213 (accept_3_4 40 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 56 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 213
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 213 (accept_3_4 37 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 213 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 213 (accept_3_4 34 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 213 (Polychromatic418967fa.accept_19_14_18_4_1_4275 33 56 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 213 (accept_3_4 31 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 213 (accept_3_4 28 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 213 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 56 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 213 (accept_3_4 25 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 213 (Polychromatic418967fa.accept_17_7_5_9_1_7763 24 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 213 (accept_3_4 22 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 56 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 213
  (Polychromatic418967fa.accept_16_4_8_5_1_3317 20 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 213 (accept_3_4 19 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 213 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 213 (accept_3_4 16 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 213 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 56 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 213 (accept_3_4 13 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 213 (accept_3_4 10 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 213 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 56 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 213 (accept_3_4 7 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  213 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 213 (accept_3_4 4 56 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 56 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 213 (Polychromatic418967fa.accept_13_2_4_5_1_3152 2
  56 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 213 (accept_3_4 1 56 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 213))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 213 (allA_succ_of_accept 54 55 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 213 (accept_3_5 53 55 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 213 (accept_3_5 50 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 213 (accept_3_5 47 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 213
  (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 213 (accept_3_5 44 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 213 (accept_3_5 41 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 213 (accept_3_5 38 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 213 (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 55 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 213 (accept_3_5 35 55 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 213
  (Polychromatic418967fa.accept_21_12_13_3_1_2124 33 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 213 (accept_3_5 32 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 213 (accept_3_5 29 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 213
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 213 (accept_3_5 26 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 213 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 213 (accept_3_5 23 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 213 (accept_3_5 20 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 213 (Polychromatic418967fa.accept_13_6_3_5_1_3167 19 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 213 (accept_3_5 17 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 213
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 213 (accept_3_5 14 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 213 (accept_3_5 11 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 213 (accept_3_5 8 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  213 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 213 (accept_3_5 5 55 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 55
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 213 (accept_3_5 2 55 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 213 (Polychromatic418967fa.accept_13_1_3_5_1_140 1
  55 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 213 (allA_succ_of_accept 53 54 213
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 52 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 213 3 17 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 50
  54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 213
  (Polychromatic418967fa.accept_10_9_4_3_1_539 49 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 213 3 16 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 54 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 213 3 15 18 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 213 3 14 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 213 (Polychromatic418967fa.accept_19_3_16_4_1_7076
  41 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 213
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 54 213 3 13 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 54 213 (Polychromatic418967fa.accept_11_5_10_4_1_1157 38 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 54 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 213 3 12 18 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 213 3 11 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 213 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  32 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 213 3 10 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 54 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 213 3 9 18 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 213
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 213 (Polychromatic418967fa.accept_13_12_2_5_1_1634 25 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 213 3 8 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 22 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 54 213 3 7 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 54 213 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 213 3 6 18 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 213
  (Polychromatic418967fa.accept_10_7_4_3_1_560 17 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 54 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 213 3 5 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 54 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 213
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 213 3 4 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 54 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 213 3 3 18 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 213 3 2 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 213 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 54 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 213
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 54 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 54 213 3 1 18 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 54 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 54 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 54 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  213)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 213 (allA_succ_of_accept 52 53 213 (accept_3_4
  52 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 213
  (Polychromatic418967fa.accept_12_3_5_9_1_176 51 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 213 (accept_3_4 49 53 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 47
  53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 213 (accept_3_4 46 53
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 213
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 45 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 213 (accept_3_4 43 53 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 213 (Polychromatic418967fa.accept_13_3_1_5_1_499 42 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 213 (accept_3_4 40 53
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 213 (Polychromatic418967fa.accept_9_3_8_6_1_80
  39 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 213 (accept_3_4 37 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 213 (Polychromatic418967fa.accept_11_2_9_4_1_310 35 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 213 (accept_3_4 34 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 213 (Polychromatic418967fa.accept_19_14_15_4_1_11248 33 53 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 213 (accept_3_4 31 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 213 (accept_3_4 28 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 53 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 213 (accept_3_4 25 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 213 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 213 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 213 (accept_3_4 22 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 53 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 213 (accept_3_4 19 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 213 (Polychromatic418967fa.accept_19_18_15_4_1_9838 18 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 213 (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 213 (accept_3_4 16 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 53 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 213 (accept_3_4 13 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 213 (accept_3_4 10 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 213 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 53 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 213
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 213 (accept_3_4 7 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  213 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 53 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 213 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 53 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 213 (accept_3_4 4 53 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 53 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 213 (accept_3_4 1 53 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 213)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 213 (allA_succ_of_accept 51 52 213 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 52 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 213 (accept_3_5 50 52 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 213 (accept_3_5 47 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 213 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 213 (accept_3_5 44 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 42 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 213 (accept_3_5 41 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 213 (accept_3_5 38 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 213
  (Polychromatic418967fa.accept_21_15_10_3_1_9578 36 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 213 (accept_3_5 35 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 213 (Polychromatic418967fa.accept_11_1_8_4_1_717 34 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 213 (accept_3_5 32 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 213 (accept_3_5 29 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 213 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 52 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 213 (accept_3_5 26 52 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 213
  (Polychromatic418967fa.accept_16_8_4_5_1_4379 24 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 213 (accept_3_5 23 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 213 (accept_3_5 20 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 213
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 213 (accept_3_5 17 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 213 (Polychromatic418967fa.accept_21_16_10_3_1_9671 16 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 213 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 213 (accept_3_5 14 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 213 (accept_3_5 11 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 213 (accept_3_5 8 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 213
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 213 (accept_3_5 5 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  213 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 52 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 52 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 213 (accept_3_5 2 52 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 213))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 213 (allA_succ_of_accept 50 51 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 213
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 51 213 3 16 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 51 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 213 3 15 17 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 213
  (Polychromatic418967fa.accept_19_6_13_4_1_876 44 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 213 3 14 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 41
  51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 51 213 3 13 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 51 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 51 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 213 3 12 17 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 213
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 213 3 11 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 213 (Polychromatic418967fa.accept_10_2_1_3_1_233 32
  51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 213 3 10 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 213 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 51 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 213 3 9 17 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 213 (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 213 3 8 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 51 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 213 3 7 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 51 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 213 3 6 17 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 213
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 213 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 213 3 5 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 213 3 4 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 213 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 213 3 3 17 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 213 3 2 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 51 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 213
  (Polychromatic418967fa.accept_13_4_12_5_1_476 4 51 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 213 3 1 17 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 51 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  213))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 213 (allA_succ_of_accept 49 50 213 (accept_3_4 49
  50 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 213
  (Polychromatic418967fa.accept_9_3_5_6_1_253 48 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 213 (accept_3_4 46 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 213 (Polychromatic418967fa.accept_13_6_11_5_1_133 45 50 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 50 213 (accept_3_4 43 50
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 50 213
  (Polychromatic418967fa.accept_12_6_2_9_1_537 42 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 50 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 213 (accept_3_4 40 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 50 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 213 (Polychromatic418967fa.accept_9_2_5_6_1_536 38
  50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 50 213 (accept_3_4 37 50
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 50 213
  (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 50 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 213 (accept_3_4 34 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 50 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 50 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 32
  50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 50 213 (accept_3_4 31 50
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 50 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 50 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 213 (accept_3_4 28 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 50 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 26
  50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 50 213 (accept_3_4 25 50
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 50 213
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 50 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 213 (accept_3_4 22 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 50 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 50 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 213 (Polychromatic418967fa.accept_9_2_5_6_1_536 20
  50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 50 213 (accept_3_4 19 50
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 50 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 50 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 213 (accept_3_4 16 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 50 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 213 (Polychromatic418967fa.accept_21_14_8_3_1_8085
  14 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 50 213 (accept_3_4 13
  50 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 50 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 50 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 213 (accept_3_4 10 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 50 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 50 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 213 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 50 213 (accept_3_4 7 50 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 6
  50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 50 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 50 213 (accept_3_4 4 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 50
  213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 50 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 213 (accept_3_4 1 50 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 213)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 213 (allA_succ_of_accept
  48 49 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 49 213 (accept_3_5 47 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 49 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 213 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 49
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 213 (accept_3_5 44 49 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 43
  49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 213
  (Polychromatic418967fa.accept_20_2_9_13_1_2599 42 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 213 (accept_3_5 41 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 213 (accept_3_5 38 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 49 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 213 (accept_3_5 35 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 213 (Polychromatic418967fa.accept_21_12_7_3_1_4927 33 49 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 213 (accept_3_5 32 49 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 213 (Polychromatic418967fa.accept_15_1_4_3_1_1928 31 49 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 213 (accept_3_5 29 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 213 (accept_3_5 26 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 49 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 213
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 213 (accept_3_5 23 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 213 (accept_3_5 20 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 49 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 213
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 213 (accept_3_5 17 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 213 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 213 (accept_3_5 14 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 213 (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 49 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 213 (accept_3_5 11 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 213 (Polychromatic418967fa.accept_16_9_1_5_1_2282 9 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 213 (accept_3_5 8 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 49 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 213
  (Polychromatic418967fa.accept_10_6_9_3_1_935 6 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 213 (accept_3_5 5 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 49 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 213 (accept_3_5 2 49 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 49 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 213))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 213 (allA_succ_of_accept 47 48 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 48 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 46
  48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 213 3 15 16 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 48 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 213 3 14 16 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 48 213 3 13 16 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 48 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 48 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 213 3 12 16 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 48 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 48 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 213 3 11 16 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 32
  48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 213 3 10 16 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 48 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 48 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 213 3 9 16 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 48 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 213 3 8 16 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 48 213 3 7 16 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 48 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 48 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 48 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 213 3 6 16 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 48 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 48 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 213 3 5 16 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 48 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 48 213 3 4 16 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 48 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 48 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 213 3 3 16 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 48 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 213 3 2 16 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 48 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 48 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 213 3 1 16 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 48 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 48 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  213)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 213 (allA_succ_of_accept 46 47 213 (accept_3_4 46 47
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 213
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 213 (accept_3_4 43 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 213 (Polychromatic418967fa.accept_9_5_2_6_1_265 41
  47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 213 (accept_3_4 40 47
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 213
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 213 (accept_3_4 37 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 213 (Polychromatic418967fa.accept_9_8_2_6_1_875 35
  47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 213 (accept_3_4 34 47
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 213
  (Polychromatic418967fa.accept_16_1_15_5_1_708 33 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 213 (accept_3_4 31 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 213 (accept_3_4 28 47
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 213
  (Polychromatic418967fa.accept_12_3_11_9_1_193 27 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 213 (accept_3_4 25 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 47 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 213 (accept_3_4 22 47
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 213
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 213 (accept_3_4 19 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 213 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 213 (accept_3_4 16 47
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 213 (accept_3_4 13 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 47 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 213
  (Polychromatic418967fa.accept_23_11_1_6_1_12576 11 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 213 (accept_3_4 10 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 213 (accept_3_4 7 47 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 213 (accept_3_4 4 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 47 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 213 (accept_3_4 1 47 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 213))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 213 (allA_succ_of_accept 45
  46 213 (Polychromatic418967fa.accept_18_9_10_15_1_7254 45 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 46 213 (accept_3_5 44 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 46 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 213 (Polychromatic418967fa.accept_11_9_2_4_1_707 42 46 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 213 (accept_3_5 41 46 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 40
  46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 213 (accept_3_5 38 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 46 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 213 (accept_3_5 35 46 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 46 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 213
  (Polychromatic418967fa.accept_19_14_8_4_1_2961 33 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 213 (accept_3_5 32 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 46 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 213 (accept_3_5 29 46 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 213 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 46 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 213 (accept_3_5 26 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 213 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 46 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 213 (accept_3_5 23 46 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 46 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 213 (accept_3_5 20 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 213 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 46 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 213 (accept_3_5 17 46 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 46 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 213 (accept_3_5 14 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 46 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 213 (accept_3_5 11 46 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 213 (Polychromatic418967fa.accept_16_10_14_5_1_5496 10 46 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 213
  (Polychromatic418967fa.accept_10_9_6_3_1_545 9 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 213 (accept_3_5 8 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 46 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 213 (accept_3_5 5 46 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 46 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 213 (accept_3_5 2 46 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  213)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 213 (allA_succ_of_accept 44 45 213
  (Polychromatic418967fa.accept_23_21_22_6_1_12575 44 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 45 213 (Polychromatic418967fa.accept_13_4_6_5_1_2333 43 45 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 213 3 14 15 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 213
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 213 (Polychromatic418967fa.accept_13_1_6_5_1_1610 40 45 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 45 213 3 13 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 45 213 (Polychromatic418967fa.accept_10_8_5_3_1_543 38
  45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 213
  (Polychromatic418967fa.accept_10_7_5_3_1_542 37 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 45 213 3 12 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 45 213 (Polychromatic418967fa.accept_18_17_9_15_1_7268 35 45 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 213 (Polychromatic418967fa.accept_16_2_13_5_1_2257 34 45
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 213 3 11 15 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 213
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 213 (Polychromatic418967fa.accept_19_12_7_4_1_9873 31 45 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 213 3 10 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 213 (Polychromatic418967fa.accept_13_3_6_5_1_2336
  29 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 213
  (Polychromatic418967fa.accept_10_8_5_3_1_543 28 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 45 213 3 9 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 45 213 (Polychromatic418967fa.accept_16_10_13_5_1_3292 26 45 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 213 (Polychromatic418967fa.accept_13_12_6_5_1_2335 25 45
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 213 3 8 15 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 213
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 213 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 45 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 213 3 7 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 213 (Polychromatic418967fa.accept_17_3_11_9_1_5100 20 45 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 213
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 45 213 3 6 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 45 213 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 45 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 213 (Polychromatic418967fa.accept_13_3_6_5_1_2336 16 45 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 213 3 5 15 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 213
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 213 (Polychromatic418967fa.accept_19_13_7_4_1_1869 13 45 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 45 213 3 4 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 45 213 (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 45 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 213
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 45 213 3 3 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 45 213 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 45 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 213 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 45 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 213 3 2 15 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 213
  (Polychromatic418967fa.accept_18_5_9_15_1_4695 5 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 45 213 (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 45 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 45 213 3 1 15 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 45 213 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 45 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 213
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 1 45 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 213))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 213 (allA_succ_of_accept 43 44 213
  (accept_3_4 43 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 213
  (Polychromatic418967fa.accept_12_6_8_9_1_553 42 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 213 (accept_3_4 40 44 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 44 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 213 (accept_3_4 37 44
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 213 (accept_3_4 34 44 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 44 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 213 (Polychromatic418967fa.accept_9_5_8_6_1_281 32
  44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 213 (accept_3_4 31 44
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 213 (Polychromatic418967fa.accept_9_3_8_6_1_80
  30 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 213 (accept_3_4 28 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 44 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 213 (accept_3_4 25 44 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 213 (Polychromatic418967fa.accept_16_8_12_5_1_200 24 44 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 213 (accept_3_4 22 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  44 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 44 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 44 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 213 (accept_3_4 19 44 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 44 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 213 (accept_3_4 16 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 213 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 44 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 213 (accept_3_4 13 44 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 44 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 44 213 (accept_3_4 10 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 44 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 213 (accept_3_4 7 44 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 44 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 213 (accept_3_4 4 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 44 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 44 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 213 (accept_3_4 1 44 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 213)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 213 (allA_succ_of_accept 42 43
  213 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 213 (accept_3_5 41 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 213 (accept_3_5 38 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 43 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 213
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 213 (accept_3_5 35 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 213 (accept_3_5 32 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 43 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 213 (accept_3_5 29 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 213 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 43 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 213 (accept_3_5 26 43 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 43 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 213
  (Polychromatic418967fa.accept_15_9_13_3_1_535 24 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 213 (accept_3_5 23 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 213 (accept_3_5 20 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 213 (accept_3_5 17 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 213 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 213 (accept_3_5 14 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 43 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 213 (accept_3_5 11 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 213 (accept_3_5 8 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 213 (Polychromatic418967fa.accept_16_7_11_5_1_4402 7 43 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 213 (accept_3_5 5 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 43 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 213 (accept_3_5 2 43 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 43 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 213))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 213
  (allA_succ_of_accept 41 42 213 (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 42 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 42 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 213 3 13 14 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 213
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 42 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 213 (Polychromatic418967fa.accept_13_11_3_5_1_982 37 42 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 213 3 12 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  42 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 213
  (Polychromatic418967fa.accept_12_10_6_9_1_549 34 42 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 42 213 3 11 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 42 213 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 42 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 213 3 10 14 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 213
  (Polychromatic418967fa.accept_16_13_10_5_1_2278 29 42 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 42 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 213 3 9 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 42 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 213
  (Polychromatic418967fa.accept_10_5_2_3_1_239 25 42 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 213 3 8 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 42 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 213 3 7 14 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 213
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 42 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 213 3 6 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 213 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 42 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 213
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 42 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 213 3 5 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 42 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 42 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 213 (Polychromatic418967fa.accept_11_2_9_4_1_310 13 42 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 213 3 4 14 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 42 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 213 3 3 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 213 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 42 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 213 3 2 14 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 213 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 42 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 213 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 42 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 213 3 1 14 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 213
  (Polychromatic418967fa.accept_11_2_9_4_1_310 2 42 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 213 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 42 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 213)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 213
  (allA_succ_of_accept 40 41 213 (accept_3_4 40 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 213 (accept_3_4 37 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 41 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 213 (accept_3_4 34 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 213 (Polychromatic418967fa.accept_13_7_2_5_1_2344 33 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 213 (accept_3_4 31 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 41 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 213
  (Polychromatic418967fa.accept_9_2_5_6_1_536 29 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 213 (accept_3_4 28 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 213 (accept_3_4 25 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 213 (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 41 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 213 (accept_3_4 22 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 213 (accept_3_4 19 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 41 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 213 (accept_3_4 16 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 213 (accept_3_4 13 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 213 (accept_3_4 10 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 213 (accept_3_4 7 41 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 213 (Polychromatic418967fa.accept_15_6_11_3_1_1172 6 41 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 213
  (Polychromatic418967fa.accept_17_5_7_9_1_5122 5 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 213 (accept_3_4 4 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 41 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 213 (accept_3_4 1 41 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 213))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 213 (allA_succ_of_accept 39 40 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 213 (accept_3_5 38 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 40 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 213 (accept_3_5 35 40 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 40 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 213
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 213 (accept_3_5 32 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 40 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 213 (accept_3_5 29 40 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 40 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 213
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 27 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 213 (accept_3_5 26 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 213 (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 40 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 213 (accept_3_5 23 40 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 40 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 213 (accept_3_5 20 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 213 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 40 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 213 (accept_3_5 17 40 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 40 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 213 (accept_3_5 14 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 40 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 213 (accept_3_5 11 40 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 40 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 213 (accept_3_5 8 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 213 (Polychromatic418967fa.accept_12_6_4_9_1_544 6 40 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 213 (accept_3_5 5 40 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 213 (Polychromatic418967fa.accept_13_4_1_5_1_1628 4 40 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 3
  40 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 213 (accept_3_5 2 40 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  213)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 213 (allA_succ_of_accept 38 39 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 39 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 213 3 12 13 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  39 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 213 3 11 13 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 39 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 39 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 213 3 10 13 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 39 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 39 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 213 3 9 13 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 39 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 213 3 8 13 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 39 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 213 3 7 13 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 39 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 39 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 213 3 6 13 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 213 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 39 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 39 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 213 3 5 13 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 39 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 213 3 4 13 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 213
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 39 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 213 3 3 13 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 39 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 39 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 213 3 2 13 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 39 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 39 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 213 3 1 13 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 39 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 213))))))))))))))))))))))))))))))))))))))) (allB_succ 38 213
  (allA_succ_of_accept 37 38 213 (accept_3_4 37 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 213 (accept_3_4 34 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 213 (Polychromatic418967fa.accept_13_7_12_5_1_1603 33 38 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 213 (accept_3_4 31 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 213 (accept_3_4 28 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 213 (accept_3_4 25 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 213 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 213 (accept_3_4 22 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 38 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 213
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 20 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 213 (accept_3_4 19 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 213 (accept_3_4 16 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 213 (accept_3_4 13 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 213 (accept_3_4 10 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 213 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 38 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 213 (accept_3_4 7 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  213 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 213 (accept_3_4 4 38 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 213 (Polychromatic418967fa.accept_13_2_12_5_1_1602
  2 38 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 213 (accept_3_4 1 38
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 213)))))))))))))))))))))))))))))))))))))) (allB_succ 37 213
  (allA_succ_of_accept 36 37 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 213 (accept_3_5 35 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 213 (accept_3_5 32 37
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 213
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 213 (accept_3_5 29 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 27
  37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 213 (accept_3_5 26 37
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 213
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 213 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 213 (accept_3_5 23 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 213 (accept_3_5 20 37
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 37 213 (Polychromatic418967fa.accept_17_1_3_9_1_958 18 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 213 (accept_3_5 17 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 37 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 213 (accept_3_5 14 37
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 37 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 213 (accept_3_5 11 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 37 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 213 (Polychromatic418967fa.accept_21_9_16_3_1_11133
  9 37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 213 (accept_3_5 8 37
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 213 (Polychromatic418967fa.accept_9_7_1_6_1_261
  7 37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 213 (accept_3_5 5 37 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 213 (accept_3_5 2 37 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 213))))))))))))))))))))))))))))))))))))) (allB_succ 36 213
  (allA_succ_of_accept 35 36 213 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 36 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 213 (Polychromatic418967fa.accept_13_8_10_5_1_977 34 36 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 213 3 11 12 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 36 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 213 (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 36 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 213 3 10 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 213 (Polychromatic418967fa.accept_10_9_6_3_1_545 29
  36 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 213
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 36 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 213 3 9 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 36 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 213 3 8 12 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 213 (Polychromatic418967fa.accept_16_6_4_5_1_2272 22 36 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 213 3 7 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 213 (Polychromatic418967fa.accept_15_5_6_3_1_525 20 36 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 213 3 6 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 213 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 36 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 36 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 213 3 5 12 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 213
  (Polychromatic418967fa.accept_21_14_15_3_1_9580 14 36 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 213 (Polychromatic418967fa.accept_19_13_17_4_1_4228 13 36 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 213 3 4 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 213
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 36 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 213 3 3 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 213 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 36 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 213 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 36 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 213 3 2 12 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 36 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 213 3 1 12 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 36 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 213
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 213)))))))))))))))))))))))))))))))))))) (allB_succ 35 213 (allA_succ_of_accept 34 35 213 (accept_3_4 34
  35 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 213
  (Polychromatic418967fa.accept_21_12_14_3_1_12574 33 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 213 (accept_3_4 31 35 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 213 (accept_3_4 28 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 213 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 213 (accept_3_4 25 35 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 213 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 35 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 213 (accept_3_4 22 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 213 (accept_3_4 19 35 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 213
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 213 (accept_3_4 16 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 213 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 213 (accept_3_4 13 35 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 35 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 213 (accept_3_4 10 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 213 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 213 (accept_3_4 7 35 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 213 (accept_3_4 4 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 35 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 213 (accept_3_4 1 35 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 213))))))))))))))))))))))))))))))))))) (allB_succ 34 213 (allA_succ_of_accept 33 34 213
  (Polychromatic418967fa.accept_19_14_15_4_1_11248 33 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 34 213 (accept_3_5 32 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 34 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 34 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 213 (accept_3_5 29 34 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 28
  34 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 213 (accept_3_5 26 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 213 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 34 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 213 (accept_3_5 23 34 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 34 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 213
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 213 (accept_3_5 20 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 34 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 213 (accept_3_5 17 34 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 34 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 213 (accept_3_5 14 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 34 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 213 (accept_3_5 11 34 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 34 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 213 (accept_3_5 8 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 34 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 213 (accept_3_5 5 34 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 34 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 213 (accept_3_5 2 34 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 213))))))))))))))))))))))))))))))))))
  (allB_succ 33 213 (allA_succ_of_accept 32 33 213 (Polychromatic418967fa.accept_19_13_14_4_1_5621 32 33 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 213
  (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 33 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 213 3 10 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 33 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 33 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 213 3 9 11 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 213
  (Polychromatic418967fa.accept_14_12_5_3_1_1011 26 33 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 213 (Polychromatic418967fa.accept_13_12_7_5_1_3147 25 33 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 213 3 8 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 33 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 22 33 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 213 3 7 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 33 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 213 (Polychromatic418967fa.accept_23_19_10_6_1_12573 19 33
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 213 3 6 11 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 213
  (Polychromatic418967fa.accept_21_17_12_3_1_4848 17 33 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 213 3 5 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 213 (Polychromatic418967fa.accept_21_14_12_3_1_9637 14 33
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 213
  (Polychromatic418967fa.accept_16_13_1_5_1_5469 13 33 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 213 3 4 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 213 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 33 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 213 (Polychromatic418967fa.accept_17_10_16_9_1_5127 10 33
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 213 3 3 11 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 213
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 33 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 213 (Polychromatic418967fa.accept_19_7_14_4_1_4268 7 33 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 213 3 2 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 213 (Polychromatic418967fa.accept_22_5_11_15_1_7870 5 33 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 33 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 213 3 1 11 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 33 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 33 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 213)))))))))))))))))))))))))))))))))
  (allB_succ 32 213 (allA_succ_of_accept 31 32 213 (accept_3_4 31 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 32 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 213 (accept_3_4 28 32 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 27
  32 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 213
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 213 (accept_3_4 25 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 213 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 213 (accept_3_4 22 32 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 32 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 213 (accept_3_4 19 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 213 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 213 (accept_3_4 16 32 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 32 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 213
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 213 (accept_3_4 13 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 213 (accept_3_4 10 32 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 213 (Polychromatic418967fa.accept_19_9_13_4_1_2982 9 32 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 213 (accept_3_4 7 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  213 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 32 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 213 (accept_3_4 4 32 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 32 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 213 (Polychromatic418967fa.accept_9_2_5_6_1_536 2
  32 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 213 (accept_3_4 1 32 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 213)))))))))))))))))))))))))))))))) (allB_succ 31 213
  (allA_succ_of_accept 30 31 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 213 (accept_3_5 29 31 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 213 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  27 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 213 (accept_3_5 26
  31 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 213
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 213 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 31 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 213 (accept_3_5 23 31 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  31 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 213 (accept_3_5 20 31
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 213 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 213 (accept_3_5 17 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 213 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 31 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 213 (accept_3_5 14 31 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 213 (Polychromatic418967fa.accept_11_2_9_4_1_310 13 31 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 213 (accept_3_5 11 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 213 (Polychromatic418967fa.accept_21_9_10_3_1_262 9 31 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 213 (accept_3_5 8 31 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 31 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 213 (accept_3_5 5 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 31 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 213 (accept_3_5 2 31 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 31 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 213))))))))))))))))))))))))))))))) (allB_succ 30 213
  (allA_succ_of_accept 29 30 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 30 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 30 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 213 3 9 10 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 213
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 30 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 30 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 213 3 8 10 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 30 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 213 3 7 10 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 30 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 213 3 6 10 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 30 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 30 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 213 3 5 10 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 30 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 213
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 30 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 213 3 4 10 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 30 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 213 3 3 10 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 30 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 213 3 2 10 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 30 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 30 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 213 3 1 10 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 30 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 30 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 213)))))))))))))))))))))))))))))) (allB_succ
  29 213 (allA_succ_of_accept 28 29 213 (accept_3_4 28 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 29 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 213 (accept_3_4 25 29 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 213 (Polychromatic418967fa.accept_10_4_9_3_1_1907
  24 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 213 (accept_3_4 22 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 213 (accept_3_4 19 29 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 29 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 213 (accept_3_4 16 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 213 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 213 (accept_3_4 13 29 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 213 (accept_3_4 10 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 213 (accept_3_4 7 29 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 213 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 29 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 213
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 213 (accept_3_4 4 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 29 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 213 (accept_3_4 1 29 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 213))))))))))))))))))))))))))))) (allB_succ 28 213 (allA_succ_of_accept 27 28 213
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 213 (accept_3_5 26 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 213 (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 28 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 213 (accept_3_5 23 28 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 28 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 28 213 (accept_3_5 20 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  28 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 28 213 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 213 (accept_3_5 17 28 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 28 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 213
  (Polychromatic418967fa.accept_10_5_8_3_1_229 15 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 213 (accept_3_5 14 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 28 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 213 (accept_3_5 11 28 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 213 (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 28 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 213
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 213 (accept_3_5 8 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 28 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 213 (accept_3_5 5 28 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 28 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 28
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 213 (accept_3_5 2 28 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 213))))))))))))))))))))))))))))
  (allB_succ 27 213 (allA_succ_of_accept 26 27 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 27 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 213 3 8 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 27 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 213 3 7 9 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 213
  (Polychromatic418967fa.accept_17_3_10_9_1_8970 20 27 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 213 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 27 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 213 3 6 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 213 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 27 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 213
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 213 3 5 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 27 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 213 3 4 9 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 213
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 27 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 213 3 3 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 213 (Polychromatic418967fa.accept_13_8_1_5_1_3176 8 27 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 213
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 27 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 213 3 2 9 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 27 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 213 3 1 9 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 27 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 213))))))))))))))))))))))))))) (allB_succ 26 213 (allA_succ_of_accept 25
  26 213 (accept_3_4 25 26 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 213
  (Polychromatic418967fa.accept_23_1_3_6_1_12572 24 26 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 213 (accept_3_4 22 26 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 26 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 213 (Polychromatic418967fa.accept_9_2_8_6_1_79 20
  26 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 213 (accept_3_4 19 26
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 213
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 26 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 213 (accept_3_4 16 26 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 213 (Polychromatic418967fa.accept_9_5_8_6_1_281 14
  26 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 213 (accept_3_4 13 26
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 213 (Polychromatic418967fa.accept_9_3_8_6_1_80
  12 26 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 26 213 (accept_3_4 10 26 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  26 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 26 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 26 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 26 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 26 213 (accept_3_4 7 26 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 26 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 26 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 26 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 26 213 (accept_3_4 4 26 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 26
  213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 26 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 26 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 213 (accept_3_4 1 26 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 213)))))))))))))))))))))))))) (allB_succ 25 213 (allA_succ_of_accept 24 25 213
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 213 (accept_3_5 23 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 25 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 213 (accept_3_5 20 25 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 25 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 213
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 213 (accept_3_5 17 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 25 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 213 (accept_3_5 14 25 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 213 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 213 (accept_3_5 11 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 213 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 25 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 213 (accept_3_5 8 25 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 213 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 25 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 213 (accept_3_5 5 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 25 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 213 (accept_3_5 2 25 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 213))))))))))))))))))))))))) (allB_succ 24 213
  (allA_succ_of_accept 23 24 213 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 24 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 213 (Polychromatic418967fa.accept_17_5_7_9_1_5122 22 24 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 213 3 7 8 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 213
  (Polychromatic418967fa.accept_11_9_2_4_1_707 20 24 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 213 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 24 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 213 3 6 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 213 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 24 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 213
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 16 24 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 213 3 5 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 213 (Polychromatic418967fa.accept_20_14_4_13_1_11212 14 24 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 213 (Polychromatic418967fa.accept_14_13_10_3_1_1037 13 24
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 213 3 4 8 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 213
  (Polychromatic418967fa.accept_16_11_8_5_1_4366 11 24 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 213 (Polychromatic418967fa.accept_15_10_9_3_1_1947 10 24 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 213 3 3 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 213 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 24 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 213
  (Polychromatic418967fa.accept_10_7_4_3_1_560 7 24 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 213 3 2 8 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 213 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 24 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 213 (Polychromatic418967fa.accept_16_4_8_5_1_3317 4 24 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 213 3 1 8 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 213
  (Polychromatic418967fa.accept_17_2_7_9_1_2796 2 24 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 213 (Polychromatic418967fa.accept_19_1_5_4_1_4246 1 24 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 213)))))))))))))))))))))))) (allB_succ 23 213 (allA_succ_of_accept 22 23
  213 (accept_3_4 22 23 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 213
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 23 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 213 (accept_3_4 19 23 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 213 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  23 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 213 (accept_3_4 16 23
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 23 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 213 (accept_3_4 13 23 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 213 (Polychromatic418967fa.accept_9_2_5_6_1_536 11
  23 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 213 (accept_3_4 10 23
  213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 213
  (Polychromatic418967fa.accept_15_9_8_3_1_557 9 23 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 23 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 213 (accept_3_4 7 23 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 23 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 5
  23 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 213 (accept_3_4 4 23 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  23 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 23 213 (accept_3_4 1 23 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23
  213))))))))))))))))))))))) (allB_succ 22 213 (allA_succ_of_accept 21 22 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 22 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 213 (accept_3_5 20 22 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 22 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 213 (accept_3_5 17 22 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 22 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 213
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 213 (accept_3_5 14 22 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 22 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 213 (accept_3_5 11 22 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 22 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 213
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 22 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 213 (accept_3_5 8 22 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 213 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 22 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 213 (accept_3_5 5 22 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 22 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 213 (accept_3_5 2 22 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 213)))))))))))))))))))))) (allB_succ 21
  213 (allA_succ_of_accept 20 21 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 21 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 21 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 213 3 6 7 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 21 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 21 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 213 3 5 7 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 21 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 21 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 213 3 4 7 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 21 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 21 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 213 3 3 7 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 213
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 21 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 213 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 21 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 213 3 2 7 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 21 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 213
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 21 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 213 3 1 7 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 213 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 21 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 21 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 213))))))))))))))))))))) (allB_succ 20 213
  (allA_succ_of_accept 19 20 213 (accept_3_4 19 20 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  20 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 20 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 20 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 213 (accept_3_4 16 20 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 20 213 (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 20 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 213
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 20 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 20 213 (accept_3_4 13 20 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  20 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 20 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 20 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 213 (accept_3_4 10 20 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 20 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 20 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 213
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 20 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 20 213 (accept_3_4 7 20 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20
  213 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 20 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 20 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 20 213 (accept_3_4 4 20 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 20 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 20 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 20 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  20 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 213 (accept_3_4 1 20 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20 213)))))))))))))))))))) (allB_succ 19 213 (allA_succ_of_accept
  18 19 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 213 (accept_3_5 17 19 213 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 19 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 213 (accept_3_5 14 19 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 213 (Polychromatic418967fa.accept_9_4_1_6_1_284 13
  19 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 213
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 19 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 213 (accept_3_5 11 19 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 213 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 19 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 213 (accept_3_5 8 19 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 213 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 19 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 213 (accept_3_5 5 19 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 213 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 19 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 213 (accept_3_5 2 19 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 19 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 213))))))))))))))))))) (allB_succ 18 213 (allA_succ_of_accept 17
  18 213 (Polychromatic418967fa.accept_19_17_18_4_1_12571 17 18 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 213 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 18 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 213 3 5 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 213 (Polychromatic418967fa.accept_11_3_7_4_1_1133
  14 18 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 213
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 18 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 213 3 4 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 213 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 18 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 213 3 3 6 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 213
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 18 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 213 3 2 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 213 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 18 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 213
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 18 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 213 3 1 6 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 213 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 18 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 213 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 18 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 213)))))))))))))))))) (allB_succ 17 213
  (allA_succ_of_accept 16 17 213 (accept_3_4 16 17 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 213 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 17 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 213 (accept_3_4 13 17 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 213 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 213
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 17 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 213 (accept_3_4 10 17 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 213 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 17 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 213 (accept_3_4 7 17 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 213 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 17 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 213
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 17 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 213 (accept_3_4 4 17 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 17 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 17 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 213 (accept_3_4 1 17 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 17 213))))))))))))))))) (allB_succ 16 213 (allA_succ_of_accept 15 16 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 213 (accept_3_5 14 16 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 16 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 213 (accept_3_5 11 16 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 16 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 213
  (Polychromatic418967fa.accept_10_9_6_3_1_545 9 16 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 213 (accept_3_5 8 16 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  213 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 213 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 16 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 213 (accept_3_5 5 16 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 213 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 16 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 16
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 213 (accept_3_5 2 16 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 213)))))))))))))))) (allB_succ 15 213
  (allA_succ_of_accept 14 15 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 15 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 213 3 4 5 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 213
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 15 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 213 3 3 5 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 213 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 15 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 213
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 15 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 213 3 2 5 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 213 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 15 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 213 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 213 3 1 5 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 213 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 15 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 213))))))))))))))) (allB_succ 14 213 (allA_succ_of_accept 13 14 213
  (accept_3_4 13 14 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 213
  (Polychromatic418967fa.accept_9_3_5_6_1_253 12 14 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 213 (accept_3_4 10 14 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 213 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 14 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 213 (Polychromatic418967fa.accept_9_8_5_6_1_538 8
  14 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 213 (accept_3_4 7 14 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 213 (Polychromatic418967fa.accept_12_6_2_9_1_537 6
  14 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 213
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 213 (accept_3_4 4 14 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 213 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 14 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 213 (accept_3_4 1 14 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 213)))))))))))))) (allB_succ 13 213 (allA_succ_of_accept 12 13 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 13 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 213 (accept_3_5 11 13 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 213 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 13 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 13 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 213 (accept_3_5 8 13 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 213 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 13 213 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 213
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 13 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 213 (accept_3_5 5 13 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  213 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 213 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 13 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 213 (accept_3_5 2 13 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 213 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 13 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 213))))))))))))) (allB_succ 12 213 (allA_succ_of_accept 11 12
  213 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 12 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 213 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 12 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 213 3 3 4 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 12 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 213
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 12 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 213 3 2 4 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 213 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 12 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 213 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 12 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 213 3 1 4 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 213
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 12 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 213 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 213)))))))))))) (allB_succ 11 213 (allA_succ_of_accept 10 11 213
  (accept_3_4 10 11 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 213
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 9 11 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 213 (accept_3_4 7 11 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 213 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  11 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 213 (accept_3_4 4 11 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 213 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  11 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 213 (accept_3_4 1 11 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  213))))))))))) (allB_succ 10 213 (allA_succ_of_accept 9 10 213 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 10 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 213 (accept_3_5 8 10 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 213
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 10 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 213 (accept_3_5 5 10 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  213 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 10 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 213 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 213 (accept_3_5 2 10 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 213 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 213)))))))))) (allB_succ 9 213 (allA_succ_of_accept 8 9 213
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 9 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 213 (Polychromatic418967fa.accept_21_7_9_3_1_8059 7 9 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 213 3 2 3 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 213 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 9 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 213
  (Polychromatic418967fa.accept_8_4_1_5_1_186 4 9 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 213 3 1 3 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 213 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 9 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 213 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 9 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 213))))))))) (allB_succ 8 213
  (allA_succ_of_accept 7 8 213 (accept_3_4 7 8 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 213
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 8 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 213 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 213 (accept_3_4 4 8 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 213 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 8 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 213 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 8
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 213 (accept_3_4 1 8 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 213)))))))) (allB_succ 7 213 (allA_succ_of_accept 6 7 213
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 213 (accept_3_5 5 7 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 213
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 213 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 7 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 213 (accept_3_5 2 7 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 213 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 7 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 213))))))) (allB_succ 6 213 (allA_succ_of_accept 5 6 213
  (Polychromatic418967fa.accept_15_5_6_3_1_525 5 6 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 213 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 6 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 213 3 1 2 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 213 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 6 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 213
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 1 6 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 213)))))) (allB_succ 5 213 (allA_succ_of_accept 4 5 213 (accept_3_4 4 5 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 213 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 5 213 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 213 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 213 (accept_3_4 1 5 213
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 213))))) (allB_succ 4 213 (allA_succ_of_accept 3 4 213
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 4 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 213 (accept_3_5 2 4 213 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 213
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 213)))) (allB_succ 3 213 (allA_succ_of_accept 2 3 213 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 213
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 213
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 3 213 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 213))) (allB_succ 2 213 (allA_succ_of_accept 1 2 213 (accept_3_4 1 2 213 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 213)) (allB_two
  213))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


