-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch237_Segment000
-- name    : Polychromatic418967fa_Branch237_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:37:16.081614+00:00
-- url     : https://prove2.me/theorems/946c9e93-1daa-4334-b1f6-38069e91d67d
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

def Polychromatic418967fa.branch_237_segment_000 : allB 100 237 :=
  allB_succ 99 237 (allA_succ_of_accept 98 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 97 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 237 3 32 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630 95 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 237 3 31 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 237
  (Polychromatic418967fa.accept_10_2_9_7_1_720 92 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 91 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 237 3 30 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 89
  99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 237
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 88 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 237 3 29 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 85 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 237 3 28 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 83 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 237 3 27 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 237 (Polychromatic418967fa.accept_15_5_9_12_1_1599
  80 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 237 3 26 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 237 (Polychromatic418967fa.accept_13_11_8_3_1_3016 76 99
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 237 3 25 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 73 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 237 3 24 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  71 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 237 3 23 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 67 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 237 3 22 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 237 (Polychromatic418967fa.accept_15_4_9_12_1_2495 64 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 237 3 21 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 237 3 20 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 237 3 19 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 237
  (Polychromatic418967fa.accept_16_8_3_13_1_7295 56 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 237 3 18 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 53
  99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 237
  (Polychromatic418967fa.accept_10_2_9_7_1_720 52 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 237 3 17 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 237 3 16 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 237 3 15 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 237 3 14 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 237 3 13 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 237 3 12 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 237 3 11 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 237 3 10 33 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 237 3 9 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 237 3 8 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 237 3 7 33 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 237
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 237 3 6 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 237 3 5 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 237 3 4 33 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 237 3 3 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 237 3 2 33 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 237 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 99 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 237 3 1 33 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 99 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  237 (allA_succ_of_accept 97 98 237 (accept_3_4 97 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 96 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 237 (accept_3_4 94 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 93 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 92 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 98 237 (accept_3_4 91 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  98 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 90 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 98 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 237 (accept_3_4 88 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 86 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 237 (accept_3_4 85 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  98 237 (Polychromatic418967fa.accept_18_12_8_3_1_1627 84 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 98 237 (accept_3_4 82 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 98 237 (Polychromatic418967fa.accept_18_9_8_3_1_2702 81 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 237
  (Polychromatic418967fa.accept_15_5_8_12_1_2435 80 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 98 237 (accept_3_4 79 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  98 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 98 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 98 237 (accept_3_4 76 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 98 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 74 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 98 237 (accept_3_4 73 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  98 237 (Polychromatic418967fa.accept_19_15_3_9_1_5962 72 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 98 237 (accept_3_4 70 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 98 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 68 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 98 237 (accept_3_4 67 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  98 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 98 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 98 237 (accept_3_4 64 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 98 237
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 62 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 98 237 (accept_3_4 61 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  98 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 237 (accept_3_4 58 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 237 (Polychromatic418967fa.accept_24_9_2_21_1_2251 57 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 98 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 98 237 (accept_3_4 55 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  98 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 98 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 237 (accept_3_4 52 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 98 237 (accept_3_4 49 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  98 237 (Polychromatic418967fa.accept_13_9_7_3_1_1531 48 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 237 (accept_3_4 46 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 98 237 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 237
  (Polychromatic418967fa.accept_19_6_3_9_1_3332 44 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 98 237 (accept_3_4 43 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  98 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 98 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 98 237 (accept_3_4 40 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 98 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 98 237 (accept_3_4 37 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  98 237 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 98 237 (accept_3_4 34 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 237 (accept_3_4 31 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 98 237 (accept_3_4 28 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 237
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 237 (accept_3_4 25 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 237 (accept_3_4 22 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 98 237 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 98 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 98 237 (accept_3_4 19 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  98 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 98 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 98 237 (accept_3_4 16 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 98 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 98 237 (accept_3_4 13 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  98 237 (Polychromatic418967fa.accept_17_12_13_16_1_3226 12 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 237 (accept_3_4 10 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 237 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 98 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 237
  (Polychromatic418967fa.accept_13_8_7_3_1_430 8 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 98 237 (accept_3_4 7 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 98
  237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 98 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 237 (accept_3_4 4 98 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 98 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  98 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 98 237 (accept_3_4 1 98 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  237 (allA_succ_of_accept 96 97 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 96 97 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 237 (accept_3_5 95 97 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 237 (Polychromatic418967fa.accept_15_3_7_12_1_372
  93 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 97 237 (accept_3_5 92
  97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 97 237
  (Polychromatic418967fa.accept_9_1_7_3_1_41 91 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 97 237 (Polychromatic418967fa.accept_22_2_9_17_1_14167 90 97 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 237 (accept_3_5 89 97 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 87
  97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 97 237 (accept_3_5 86 97
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 97 237 (Polychromatic418967fa.accept_9_4_7_3_1_43
  85 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 97 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 84 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 97 237 (accept_3_5 83 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 97 237 (Polychromatic418967fa.accept_15_6_7_12_1_869 81 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 237 (accept_3_5 80 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 97 237 (Polychromatic418967fa.accept_13_1_6_3_1_1547 79 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 78 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 237 (accept_3_5 77 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 75 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 237 (accept_3_5 74 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 237
  (Polychromatic418967fa.accept_19_15_2_9_1_10357 72 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 237 (accept_3_5 71 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 237 (accept_3_5 68 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 237
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 66 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 237 (accept_3_5 65 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 237 (accept_3_5 62 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 237 (Polychromatic418967fa.accept_13_9_6_3_1_1514 61 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 60 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 237 (accept_3_5 59 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 237 (Polychromatic418967fa.accept_13_5_6_3_1_868 57 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 237 (accept_3_5 56 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 237
  (Polychromatic418967fa.accept_34_20_29_33_1_14166 54 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 97 237 (accept_3_5 53 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 97 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 237 (accept_3_5 50 97 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 49
  97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 237
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 237 (accept_3_5 47 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 237 (Polychromatic418967fa.accept_17_11_12_16_1_3219 45 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 237 (accept_3_5 44 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 237 (Polychromatic418967fa.accept_31_12_4_20_1_14165 43 97
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 237 (accept_3_5 41 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 237 (accept_3_5 38 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 237 (accept_3_5 35 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 237 (accept_3_5 32 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 237
  (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 237 (accept_3_5 29 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 237 (accept_3_5 26 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 237 (Polychromatic418967fa.accept_11_3_9_6_1_105 25 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 237 (accept_3_5 23 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 237 (Polychromatic418967fa.accept_15_6_7_12_1_869 21 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 237 (accept_3_5 20 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 237
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 237 (accept_3_5 17 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 237 (accept_3_5 14 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 237 (accept_3_5 11 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 237 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 237 (accept_3_5 8 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 237 (Polychromatic418967fa.accept_19_7_2_9_1_6006 7 97 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 237 (accept_3_5 5 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 237 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 97 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 237 (accept_3_5 2 97 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 97 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 96 237
  (allA_succ_of_accept 95 96 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 95 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 94 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 96 237 3 31 32 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 96 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 92 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 96 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 91 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 237 3 30 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 89
  96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 96 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 88 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 96 237 3 29 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 96 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 86 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 96 237 3 28 32 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 96 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 96 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 82 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 237 3 27 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 80
  96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 96 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 79 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 237 3 26 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 96 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 96 237 3 25 32 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 96 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 74 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 96 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 237 3 24 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 71
  96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 96 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 70 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 96 237 3 23 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 96 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 237 3 22 32 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 96 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 237 3 21 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 96 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 237 3 20 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 96 237 3 19 32 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 96 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 96 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 237 3 18 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 53
  96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 96 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 96 237 3 17 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 96 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 237 3 16 32 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 96 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 237 3 15 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 44
  96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 237 3 14 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 96 237 3 13 32 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 96 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 96 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 237 3 12 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 96 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 96 237 3 11 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 96 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 237 3 10 32 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 96 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 237 3 9 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 237 3 8 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 96 237 3 7 32 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 96 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 96 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 237 3 6 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 96 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 96 237 3 5 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 96 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 237 3 4 32 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 96 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 237 3 3 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 237 3 2 32 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 96 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 96 237 3 1 32 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 96 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 96 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 96 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 96 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 96
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 237
  (allA_succ_of_accept 94 95 237 (accept_3_4 94 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 237 (accept_3_4 91 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 89 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 237 (accept_3_4 88 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 237 (accept_3_4 85 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 237 (Polychromatic418967fa.accept_15_9_5_12_1_1640 84 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 83 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 237 (accept_3_4 82 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 237 (Polychromatic418967fa.accept_15_6_5_12_1_1642 81 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 237 (accept_3_4 79 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 237
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 77 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 237 (accept_3_4 76 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 237 (accept_3_4 73 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 71 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 237 (accept_3_4 70 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 237 (accept_3_4 67 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 237 (accept_3_4 64 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 237 (accept_3_4 61 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 237 (accept_3_4 58 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 237 (Polychromatic418967fa.accept_17_6_10_16_1_9453 57 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 237 (accept_3_4 55 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 237 (accept_3_4 52 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 237 (accept_3_4 49 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 237 (accept_3_4 46 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 237 (accept_3_4 43 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 237
  (Polychromatic418967fa.accept_17_7_10_16_1_5582 41 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 237 (accept_3_4 40 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 237 (accept_3_4 37 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 237 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 237 (accept_3_4 34 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 237 (accept_3_4 31 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 237 (accept_3_4 28 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 237 (accept_3_4 25 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 237 (accept_3_4 22 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 237 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 237 (accept_3_4 19 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 237 (accept_3_4 16 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 237 (accept_3_4 13 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 237 (accept_3_4 10 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 237 (accept_3_4 7 95 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 237 (accept_3_4 4 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  237 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 95 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 237 (accept_3_4 1 95 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 237
  (allA_succ_of_accept 93 94 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 237 (accept_3_5 92 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 237 (Polychromatic418967fa.accept_12_6_10_9_1_531
  90 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 237 (accept_3_5 89
  94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 88 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 237 (accept_3_5 86 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 237 (Polychromatic418967fa.accept_15_9_4_12_1_1611
  84 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 237 (accept_3_5 83
  94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 237
  (Polychromatic418967fa.accept_9_1_4_3_1_201 82 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 94 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 94 237 (accept_3_5 80 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 94 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 78
  94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 237 (accept_3_5 77 94
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 237
  (Polychromatic418967fa.accept_15_1_4_12_1_2401 76 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 237 (accept_3_5 74 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 94 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 72
  94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 94 237 (accept_3_5 71 94
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 94 237
  (Polychromatic418967fa.accept_9_7_4_3_1_204 70 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 94 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 237 (accept_3_5 68 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 237 (Polychromatic418967fa.accept_12_6_10_9_1_531
  66 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 94 237 (accept_3_5 65
  94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 94 237
  (Polychromatic418967fa.accept_9_1_4_3_1_201 64 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 237 (accept_3_5 62 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 94 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 60
  94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 94 237 (accept_3_5 59 94
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 94 237 (Polychromatic418967fa.accept_7_2_3_6_1_4
  58 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 94 237
  (Polychromatic418967fa.accept_17_6_9_16_1_4410 57 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 94 237 (accept_3_5 56 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 94 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 94 237 (accept_3_5 53 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 94 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 94 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 94 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 94 237 (accept_3_5 50 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  94 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 94 237 (Polychromatic418967fa.accept_19_10_18_9_1_11636 48 94 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 94 237 (accept_3_5 47 94 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 94 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 94 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 237
  (Polychromatic418967fa.accept_14_3_10_13_1_339 45 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 94 237 (accept_3_5 44 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 94 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 94 237 (accept_3_5 41 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 94 237 (Polychromatic418967fa.accept_17_6_9_16_1_4410 40 94 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 94 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 94 237 (accept_3_5 38 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  94 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 94 237 (Polychromatic418967fa.accept_21_15_10_6_1_11306 36 94 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 94 237 (accept_3_5 35 94 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 94 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 94 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 94 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 94 237 (accept_3_5 32 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 94 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 94 237 (accept_3_5 29 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 94 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 94 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 94 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 94 237 (accept_3_5 26 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  94 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 94 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 94 237 (accept_3_5 23 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 94 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 94 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 94 237
  (Polychromatic418967fa.accept_10_1_4_7_1_374 21 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 94 237 (accept_3_5 20 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 94 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 94 237 (accept_3_5 17 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 94 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 94 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 94 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 94 237 (accept_3_5 14 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  94 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 94 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 94 237 (accept_3_5 11 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 94 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 94 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 94 237 (accept_3_5 8 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94
  237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 94 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 94 237 (accept_3_5 5 94 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 94 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 94 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 94 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 237 (accept_3_5 2 94 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 237
  (allA_succ_of_accept 92 93 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 92 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 237 (Polychromatic418967fa.accept_21_7_9_6_1_8212 91 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 237 3 30 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 237
  (Polychromatic418967fa.accept_11_1_5_6_1_397 89 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 237 3 29 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 237 (Polychromatic418967fa.accept_10_6_3_7_1_2197
  86 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 237 3 28 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 237 (Polychromatic418967fa.accept_13_5_2_3_1_1526 83 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 237 (Polychromatic418967fa.accept_15_7_3_12_1_365 82 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 237 3 27 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 237 (Polychromatic418967fa.accept_13_1_2_3_1_911 79 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 237 3 26 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 237 (Polychromatic418967fa.accept_13_12_2_3_1_1527
  77 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 237
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 76 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 237 3 25 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 74 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 237 3 24 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 93 237 (Polychromatic418967fa.accept_13_5_2_3_1_1526 70 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 237 3 23 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 237 (Polychromatic418967fa.accept_15_8_3_12_1_1657
  68 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 93 237 3 22 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 93 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 237 3 21 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 237
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 62 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 237 (Polychromatic418967fa.accept_13_9_2_3_1_3027 61 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 237 3 20 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 237
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 58 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 237 3 19 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 237 (Polychromatic418967fa.accept_10_6_3_7_1_2197 56 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 237 3 18 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 237 3 17 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 50
  93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 237
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 237 3 16 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 237 (Polychromatic418967fa.accept_15_2_3_12_1_891 47 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 237 3 15 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 237
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 237 3 14 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 237 (Polychromatic418967fa.accept_17_7_8_16_1_6966
  41 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 237
  (Polychromatic418967fa.accept_13_1_2_3_1_911 40 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 237 3 13 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 237 (Polychromatic418967fa.accept_13_11_2_3_1_883 37 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 237 3 12 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 237
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 237 (Polychromatic418967fa.accept_10_4_3_7_1_1110 34 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 237 3 11 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 32
  93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 93 237 3 10 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 93 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 237 (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 93
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 237 3 9 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 237
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 26 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 93 237 3 8 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 93 237 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 93 237 3 7 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 93 237 (Polychromatic418967fa.accept_19_1_17_9_1_2150 20 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 237 (Polychromatic418967fa.accept_17_2_8_16_1_4403 19 93
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 237 3 6 31 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 237 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 93 237 3 5 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 93 237 (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 237
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 93 237 3 4 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 93 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 237 3 3 31 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 237 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 93 237 3 2 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 93 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 93 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 93 237 3 1 31 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 93 237 (Polychromatic418967fa.accept_15_2_3_12_1_891 2 93 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 93 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 237
  (allA_succ_of_accept 91 92 237 (accept_3_4 91 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 90 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 237 (accept_3_4 88 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 237 (accept_3_4 85 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 84 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 237 (accept_3_4 82 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 80 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 237 (accept_3_4 79 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 237 (accept_3_4 76 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 237
  (Polychromatic418967fa.accept_10_4_2_7_1_373 74 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 237 (accept_3_4 73 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 237 (accept_3_4 70 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 237 (accept_3_4 67 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 237 (accept_3_4 64 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 237 (Polychromatic418967fa.accept_13_11_1_3_1_910 63 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 62 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 237 (accept_3_4 61 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 237 (accept_3_4 58 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 237
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 56 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 237 (accept_3_4 55 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 237 (accept_3_4 52 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 237 (accept_3_4 49 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 237 (Polychromatic418967fa.accept_15_3_2_12_1_2469 48 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 237 (accept_3_4 46 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 237 (accept_3_4 43 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 237 (accept_3_4 40 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096 39 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 237
  (Polychromatic418967fa.accept_25_13_17_12_1_14164 38 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 92 237 (accept_3_4 37 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 92 237 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 92 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 237 (accept_3_4 34 92 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 33
  92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 237 (accept_3_4 31 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 237 (accept_3_4 28 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 237 (Polychromatic418967fa.accept_17_10_7_16_1_6841 27 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 237 (accept_3_4 25 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 237 (accept_3_4 22 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 237 (Polychromatic418967fa.accept_14_7_8_13_1_3161 21 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 237
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 237 (accept_3_4 19 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 237 (accept_3_4 16 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 237 (accept_3_4 13 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 237 (accept_3_4 10 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 92 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 237 (accept_3_4 7 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 237 (accept_3_4 4 92 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 237 (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 92 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  92 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 237 (accept_3_4 1 92 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 237
  (allA_succ_of_accept 90 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 237 (accept_3_5 89 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 87
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 237 (accept_3_5 86 91
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 85 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 91 237 (Polychromatic418967fa.accept_10_4_1_7_1_371 84 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 91 237 (accept_3_5 83 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 91 237 (Polychromatic418967fa.accept_18_9_1_3_1_6451
  81 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 237 (accept_3_5 80
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 237
  (Polychromatic418967fa.accept_9_7_1_3_1_443 79 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 91 237 (accept_3_5 77 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 91 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 91 237 (Polychromatic418967fa.accept_11_9_3_6_1_797
  75 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 237 (accept_3_5 74
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 237
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 73 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 91 237 (Polychromatic418967fa.accept_16_8_11_13_1_7265 72 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 91 237 (accept_3_5 71 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 91 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 69
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 237 (accept_3_5 68 91
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 67 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 91 237 (accept_3_5 65 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 91 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 91 237 (Polychromatic418967fa.accept_11_8_3_6_1_1855
  63 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 237 (accept_3_5 62
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 237
  (Polychromatic418967fa.accept_9_7_1_3_1_443 61 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 91 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 60 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 237 (accept_3_5 59 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 237 (Polychromatic418967fa.accept_14_1_7_13_1_333
  57 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 237 (accept_3_5 56
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 237
  (Polychromatic418967fa.accept_21_13_7_6_1_3656 55 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 237 (accept_3_5 53 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 91 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 51
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 237 (accept_3_5 50 91
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 91 237 (Polychromatic418967fa.accept_14_6_7_13_1_3158 48 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 237 (accept_3_5 47 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 237 (Polychromatic418967fa.accept_18_9_1_3_1_6451
  45 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 237 (accept_3_5 44
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 237
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 237 (accept_3_5 41 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 91 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  39 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 237 (accept_3_5 38
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 237
  (Polychromatic418967fa.accept_19_18_15_9_1_3310 37 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 91 237 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 237 (accept_3_5 35 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 33
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 237 (accept_3_5 32 91
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 237 (accept_3_5 29 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 91 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  27 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 237 (accept_3_5 26
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 237
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 91 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 237 (accept_3_5 23 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 237 (Polychromatic418967fa.accept_19_2_15_9_1_7318
  21 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 237 (accept_3_5 20
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 237
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 19 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 237 (accept_3_5 17 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 91 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 15
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 237 (accept_3_5 14 91
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 91 237 (Polychromatic418967fa.accept_18_12_1_3_1_7843 12 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 237 (accept_3_5 11 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 91 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 237 (Polychromatic418967fa.accept_11_9_3_6_1_797 9
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 237 (accept_3_5 8 91 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 7
  91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 237 (accept_3_5 5 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 237 (accept_3_5 2 91 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 237 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 91 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 237
  (allA_succ_of_accept 89 90 237 (Polychromatic418967fa.accept_14_5_6_13_1_3145 89 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 88 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 237 3 29 30 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 237
  (Polychromatic418967fa.accept_12_2_6_9_1_19 86 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 90 237 (Polychromatic418967fa.accept_16_5_10_13_1_6042 85 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 237 3 28 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 83
  90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 237
  (Polychromatic418967fa.accept_12_10_6_9_1_549 82 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 90 237 3 27 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 90 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608 80 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 237 3 26 30 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 237
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 77 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 90 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 76 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 237 3 25 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 74
  90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 90 237
  (Polychromatic418967fa.accept_19_16_14_9_1_7316 73 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 90 237 3 24 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 90 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 237 (Polychromatic418967fa.accept_11_4_2_6_1_389 70 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 90 237 3 23 30 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 90 237
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 68 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 90 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 237 3 22 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 237 (Polychromatic418967fa.accept_19_8_14_9_1_4590
  65 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 90 237
  (Polychromatic418967fa.accept_12_4_6_9_1_548 64 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 90 237 3 21 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 90 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 62 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 237 (Polychromatic418967fa.accept_13_9_12_3_1_907 61 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 237 3 20 30 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 90 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 90 237 3 19 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 90 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  56 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 90 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 90 237 3 18 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 237 (Polychromatic418967fa.accept_16_5_10_13_1_6042 53 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 52 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 90 237 3 17 30 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 90 237
  (Polychromatic418967fa.accept_12_2_6_9_1_19 50 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 90 237 (Polychromatic418967fa.accept_14_7_6_13_1_4111 49 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 237 3 16 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 237
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 90 237 3 15 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 90 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 237 3 14 30 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 237
  (Polychromatic418967fa.accept_13_2_12_3_1_415 41 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 90 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 90 237 3 13 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 38
  90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 237
  (Polychromatic418967fa.accept_11_4_2_6_1_389 37 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 237 3 12 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 90 237 3 11 30 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 90 237
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 90 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 237 3 10 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 237
  (Polychromatic418967fa.accept_20_9_10_17_1_14163 29 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 90 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 90 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 90 237 3 9 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 90 237 (Polychromatic418967fa.accept_11_4_2_6_1_389 26
  90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 237
  (Polychromatic418967fa.accept_19_6_14_9_1_8863 25 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 237 3 8 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 237 3 7 30 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 237
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 90 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 237 3 6 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 237 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 237
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 90 237 3 5 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 90 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 237 (Polychromatic418967fa.accept_20_13_10_17_1_5510 13 90
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 237 3 4 30 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 90 237 3 3 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 90 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 237 3 2 30 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 90 237 (Polychromatic418967fa.accept_14_5_6_13_1_3145 5 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 237 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 90 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 237 3 1 30 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 237
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 90 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 237 (Polychromatic418967fa.accept_17_1_5_16_1_5589 1 90 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 237
  (allA_succ_of_accept 88 89 237 (accept_3_4 88 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 237 (accept_3_4 85 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 83 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 237 (accept_3_4 82 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 237 (accept_3_4 79 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 77 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 237 (accept_3_4 76 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 237 (accept_3_4 73 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 237 (accept_3_4 70 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 237 (accept_3_4 67 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 237 (Polychromatic418967fa.accept_13_1_11_3_1_901 66 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 65 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 237 (accept_3_4 64 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 237 (accept_3_4 61 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 59 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 237 (accept_3_4 58 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 237 (accept_3_4 55 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 237 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 237 (accept_3_4 52 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 237 (accept_3_4 49 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 47 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 237 (accept_3_4 46 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 237 (Polychromatic418967fa.accept_19_7_13_9_1_10179 45 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 237 (accept_3_4 43 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 237 (accept_3_4 40 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 237 (accept_3_4 37 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 237
  (Polychromatic418967fa.accept_25_10_14_12_1_14162 35 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 89 237 (accept_3_4 34 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 89 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 89 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 237 (accept_3_4 31 89 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 237
  (Polychromatic418967fa.accept_20_10_9_17_1_12902 30 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 237 (accept_3_4 28 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 237 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 237 (accept_3_4 25 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 237 (accept_3_4 22 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 237 (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 237 (accept_3_4 19 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 237 (Polychromatic418967fa.accept_15_2_14_12_1_2453 17 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 237 (accept_3_4 16 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 89 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 237 (accept_3_4 13 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 237 (accept_3_4 10 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 237 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 89 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 237 (accept_3_4 7 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 89 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 89 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 237 (accept_3_4 4 89 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 89 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 237 (accept_3_4 1 89 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 88 237
  (allA_succ_of_accept 87 88 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 88 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 237 (accept_3_5 86 88 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 237 (Polychromatic418967fa.accept_13_6_10_3_1_897
  84 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 88 237 (accept_3_5 83
  88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 88 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 82 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 88 237 (Polychromatic418967fa.accept_17_13_3_16_1_5599 81 88 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 237 (accept_3_5 80 88 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 78
  88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 88 237 (accept_3_5 77 88
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 88 237 (Polychromatic418967fa.accept_9_4_7_3_1_43
  76 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 88 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 88 237 (accept_3_5 74 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 88 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 88 237 (accept_3_5 71 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 88 237 (Polychromatic418967fa.accept_15_10_13_12_1_3384 70 88 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 88 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 69 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 88 237 (accept_3_5 68 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 88 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 88 237 (accept_3_5 65 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 88 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 88 237
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 88 237 (accept_3_5 62 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 88 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 88 237 (accept_3_5 59 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 88 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 88 237
  (Polychromatic418967fa.accept_21_15_4_6_1_11286 57 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 237 (accept_3_5 56 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 237 (accept_3_5 53 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 237 (accept_3_5 50 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 237 (Polychromatic418967fa.accept_15_3_13_12_1_348 48 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 237 (accept_3_5 47 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 88 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 237 (accept_3_5 44 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 237 (accept_3_5 41 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 237
  (Polychromatic418967fa.accept_10_9_8_7_1_714 39 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 237 (accept_3_5 38 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 237 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 237 (accept_3_5 35 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 237 (Polychromatic418967fa.accept_21_13_4_6_1_6668 34 88
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 237 (accept_3_5 32 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 237 (accept_3_5 29 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 237
  (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 237 (accept_3_5 26 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 237 (accept_3_5 23 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 237
  (Polychromatic418967fa.accept_16_5_8_13_1_2764 21 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 237 (accept_3_5 20 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 237 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 237 (accept_3_5 17 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 237 (accept_3_5 14 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 237 (accept_3_5 11 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 88 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 237 (accept_3_5 8 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 88 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 88 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 237 (accept_3_5 5 88 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 88 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 88 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  88 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 237 (accept_3_5 2 88 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 237
  (allA_succ_of_accept 86 87 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 85 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 237 3 28 29 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 237 3 27 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 80
  87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 237 3 26 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 237 3 25 29 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 237 3 24 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 71
  87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 237 3 23 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 237 3 22 29 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 237 3 21 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 237 3 20 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 237 3 19 29 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 237 3 18 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 53
  87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 237 3 17 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 237 3 16 29 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 237 3 15 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 87
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 237 3 14 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 237 3 13 29 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 237 3 12 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 237 3 11 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 237 3 10 29 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 237 3 9 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 237 3 8 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 237 3 7 29 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 237 3 6 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 237 3 5 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 237 3 4 29 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 237 3 3 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 237 3 2 29 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 87 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 237 3 1 29 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 87 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 237
  (allA_succ_of_accept 85 86 237 (accept_3_4 85 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 237 (Polychromatic418967fa.accept_16_4_6_13_1_1874 84 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 237 (accept_3_4 82 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 237 (accept_3_4 79 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 237 (accept_3_4 76 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 237 (accept_3_4 73 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 237 (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 237 (accept_3_4 70 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 237
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 68 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 237 (accept_3_4 67 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 237 (accept_3_4 64 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 62 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 237 (accept_3_4 61 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 237 (accept_3_4 58 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 237 (accept_3_4 55 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 237 (accept_3_4 52 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 237 (accept_3_4 49 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 237 (Polychromatic418967fa.accept_13_9_8_3_1_3045 48 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 237 (accept_3_4 46 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 44 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 237 (accept_3_4 43 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 237 (accept_3_4 40 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 237 (accept_3_4 37 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 237 (accept_3_4 34 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 237 (accept_3_4 31 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 237 (accept_3_4 28 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 237 (accept_3_4 25 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 237 (accept_3_4 22 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 237 (accept_3_4 19 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 237 (accept_3_4 16 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 237
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 237 (accept_3_4 13 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 237 (Polychromatic418967fa.accept_17_12_1_16_1_4360 12 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 237 (accept_3_4 10 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 237 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 86 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 237 (accept_3_4 7 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 86 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 237 (accept_3_4 4 86 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 86
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 237 (accept_3_4 1 86 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 237
  (allA_succ_of_accept 84 85 237 (Polychromatic418967fa.accept_15_9_10_12_1_1625 84 85 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 237 (accept_3_5 83 85 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 237
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 81 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 85 237 (accept_3_5 80 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  85 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 85 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 78 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 237 (accept_3_5 77 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 85 237 (accept_3_5 74 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  85 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 85 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 237 (accept_3_5 71 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 69 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 85 237 (accept_3_5 68 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  85 237 (Polychromatic418967fa.accept_15_7_10_12_1_2403 67 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 85 237 (Polychromatic418967fa.accept_13_1_7_3_1_1503 66 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 237 (accept_3_5 65 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 237
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 85 237 (accept_3_5 62 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  85 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 85 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 237 (accept_3_5 59 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 237
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 57 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 85 237 (accept_3_5 56 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  85 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 85 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 237 (accept_3_5 53 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 85 237 (accept_3_5 50 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  85 237 (Polychromatic418967fa.accept_13_10_7_3_1_3041 49 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 85 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 237 (accept_3_5 47 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 237
  (Polychromatic418967fa.accept_18_9_13_3_1_5088 45 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 85 237 (accept_3_5 44 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  85 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 85 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 237 (accept_3_5 41 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 237
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 85 237 (accept_3_5 38 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  85 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 85 237 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 237 (accept_3_5 35 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 85 237 (accept_3_5 32 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  85 237 (Polychromatic418967fa.accept_20_11_5_17_1_5490 31 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 85 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 237 (accept_3_5 29 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 237
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 85 237 (accept_3_5 26 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  85 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 85 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 237 (accept_3_5 23 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 237
  (Polychromatic418967fa.accept_13_8_7_3_1_430 21 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 85 237 (accept_3_5 20 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  85 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 85 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 237 (accept_3_5 17 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 85 237 (accept_3_5 14 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  85 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 85 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 237 (accept_3_5 11 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 85 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 85 237 (accept_3_5 8 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85
  237 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 85 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 85 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 85 237 (accept_3_5 5 85 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 85 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 3
  85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 237 (accept_3_5 2 85 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  85 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 237
  (allA_succ_of_accept 83 84 237 (Polychromatic418967fa.accept_10_3_4_7_1_353 83 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 82 84 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 237 3 27 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 237
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 80 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 237 (Polychromatic418967fa.accept_13_1_6_3_1_1547 79 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 237 3 26 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 237 (Polychromatic418967fa.accept_19_1_8_9_1_3304
  77 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 84 237
  (Polychromatic418967fa.accept_16_12_4_13_1_3827 76 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 84 237 3 25 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 84 237 (Polychromatic418967fa.accept_13_9_6_3_1_1514 74 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 84 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 73 84 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 237 3 24 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 237
  (Polychromatic418967fa.accept_10_1_4_7_1_374 71 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 84 237 (Polychromatic418967fa.accept_13_5_6_3_1_868 70 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 84 237 3 23 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 237 (Polychromatic418967fa.accept_18_14_12_3_1_5103
  68 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 84 237
  (Polychromatic418967fa.accept_11_1_7_6_1_378 67 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 237 3 22 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 237 (Polychromatic418967fa.accept_15_4_9_12_1_2495 64 84
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 84 237 3 21 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 84 237
  (Polychromatic418967fa.accept_10_2_4_7_1_352 62 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 84 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 61 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 237 3 20 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 237 (Polychromatic418967fa.accept_15_14_9_12_1_2498
  59 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 237
  (Polychromatic418967fa.accept_19_1_8_9_1_3304 58 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 84 237 3 19 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 84 237 (Polychromatic418967fa.accept_11_1_7_6_1_378 56 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 84 237 (Polychromatic418967fa.accept_15_10_9_12_1_2497 55 84
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 237 3 18 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 237
  (Polychromatic418967fa.accept_10_3_4_7_1_353 53 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 237 3 17 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 237 (Polychromatic418967fa.accept_15_5_9_12_1_1599
  50 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 84 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 84 237 3 16 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 84 237 (Polychromatic418967fa.accept_20_7_4_17_1_4132 47 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 237 (Polychromatic418967fa.accept_25_21_9_12_1_14161 46 84
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 237 3 15 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 237
  (Polychromatic418967fa.accept_13_5_6_3_1_868 44 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 84 237 (Polychromatic418967fa.accept_10_3_4_7_1_353 43 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 237 3 14 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 41
  84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 237
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 40 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 84 237 3 13 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 84 237 (Polychromatic418967fa.accept_16_6_4_13_1_3841 38 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 84 237 (Polychromatic418967fa.accept_18_1_12_3_1_6426 37 84
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 237 3 12 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 237
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 84 237 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 237 3 11 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 32
  84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 84 237
  (Polychromatic418967fa.accept_10_1_4_7_1_374 31 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 237 3 10 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 237 (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 237 (Polychromatic418967fa.accept_16_12_4_13_1_3827 28 84
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 84 237 3 9 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 237
  (Polychromatic418967fa.accept_18_8_12_3_1_2708 26 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 237 3 8 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 237 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 84 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 237
  (Polychromatic418967fa.accept_10_2_4_7_1_352 22 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 84 237 3 7 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 84 237 (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 237 (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 84
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 237 3 6 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 237 (Polychromatic418967fa.accept_19_16_8_9_1_8858 16 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 237 3 5 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 84 237 (Polychromatic418967fa.accept_13_1_6_3_1_1547 14 84 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 84 237
  (Polychromatic418967fa.accept_10_3_4_7_1_353 13 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 237 3 4 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 11 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 237 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 84
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 237 3 3 28 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 237
  (Polychromatic418967fa.accept_16_8_4_13_1_1014 8 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 84 237 (Polychromatic418967fa.accept_16_7_4_13_1_1057 7 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 237 3 2 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 237 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 84 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 84 237
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 84 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 84 237 3 1 28 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 84 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 84 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 84 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 237
  (allA_succ_of_accept 82 83 237 (accept_3_4 82 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 237 (Polychromatic418967fa.accept_16_1_3_13_1_2785 81 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 237 (accept_3_4 79 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 237 (accept_3_4 76 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 75 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 237 (accept_3_4 73 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 237 (Polychromatic418967fa.accept_16_8_3_13_1_7295 72 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 71 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 237 (accept_3_4 70 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 237 (accept_3_4 67 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 237
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 65 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 237 (accept_3_4 64 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 237 (accept_3_4 61 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 237 (accept_3_4 58 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 237 (Polychromatic418967fa.accept_21_15_20_6_1_6625 57 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 237 (accept_3_4 55 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 237 (accept_3_4 52 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 237 (accept_3_4 49 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 237
  (Polychromatic418967fa.accept_13_8_5_3_1_427 47 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 237 (accept_3_4 46 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 237 (accept_3_4 43 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 237 (accept_3_4 40 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 237 (accept_3_4 37 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 237 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 237 (accept_3_4 34 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 237 (accept_3_4 31 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 237
  (Polychromatic418967fa.accept_19_10_7_9_1_10345 29 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 237 (accept_3_4 28 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 237 (accept_3_4 25 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 237 (accept_3_4 22 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 237 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 237 (accept_3_4 19 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 237 (accept_3_4 16 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 237 (accept_3_4 13 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 237 (Polychromatic418967fa.accept_24_12_11_21_1_7280 12 83 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 237
  (Polychromatic418967fa.accept_13_11_5_3_1_889 11 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 237 (accept_3_4 10 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 237 (accept_3_4 7 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 237 (accept_3_4 4 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  237 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 83 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 237 (accept_3_4 1 83 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 237
  (allA_succ_of_accept 81 82 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 237 (accept_3_5 80 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 78
  82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 237 (accept_3_5 77 82
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 76 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 237 (accept_3_5 74 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 82 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 237 (Polychromatic418967fa.accept_13_7_4_3_1_3064
  72 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 237 (accept_3_5 71
  82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 237
  (Polychromatic418967fa.accept_9_7_1_3_1_443 70 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 82 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 237 (accept_3_5 68 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 237 (Polychromatic418967fa.accept_12_6_10_9_1_531
  66 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 237 (accept_3_5 65
  82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 64 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 237 (accept_3_5 62 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 82 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 60
  82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 237 (accept_3_5 59 82
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 58 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 82 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 237 (accept_3_5 56 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 237 (Polychromatic418967fa.accept_10_4_2_7_1_373
  54 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 237 (accept_3_5 53
  82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 237
  (Polychromatic418967fa.accept_9_7_1_3_1_443 52 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 237 (accept_3_5 50 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 82 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 237
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 48 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 237 (accept_3_5 47 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 237 (accept_3_5 44 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 237 (accept_3_5 41 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 237 (accept_3_5 38 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 82 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 237 (accept_3_5 35 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 237 (accept_3_5 32 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 237
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 237 (accept_3_5 29 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 237 (Polychromatic418967fa.accept_17_11_14_16_1_1270 28 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 237 (accept_3_5 26 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 82 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 237 (accept_3_5 23 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 237 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 82 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 237 (accept_3_5 20 82 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 237 (accept_3_5 17 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 237 (accept_3_5 14 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 237
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 237 (accept_3_5 11 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 237 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 237 (accept_3_5 8 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 237 (accept_3_5 5 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  237 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 82 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 237 (accept_3_5 2 82 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 237
  (allA_succ_of_accept 80 81 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 81 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 237 3 26 27 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 237
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 77 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 81 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 76 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 237 3 25 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 237 (Polychromatic418967fa.accept_10_4_1_7_1_371 74
  81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 81 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 81 237 3 24 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 81 237 (Polychromatic418967fa.accept_17_3_13_16_1_2183 71 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 237 (Polychromatic418967fa.accept_15_10_6_12_1_1645 70 81
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 81 237 3 23 27 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 81 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 237 (Polychromatic418967fa.accept_15_7_6_12_1_1614 67 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 237 3 22 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 65
  81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 237
  (Polychromatic418967fa.accept_10_4_1_7_1_371 64 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 81 237 3 21 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 237 (Polychromatic418967fa.accept_15_2_6_12_1_1613 62 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 81 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 237 3 20 27 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 237 3 19 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 237 (Polychromatic418967fa.accept_10_6_1_7_1_342 56
  81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 237
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 55 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 237 3 18 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 237 (Polychromatic418967fa.accept_16_5_1_13_1_1053 53 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 81 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 237 3 17 27 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 237
  (Polychromatic418967fa.accept_15_5_6_12_1_916 50 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 237 (Polychromatic418967fa.accept_18_13_9_3_1_5114 49 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 237 3 16 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 237
  (Polychromatic418967fa.accept_10_6_1_7_1_342 46 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 237 3 15 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 237 (Polychromatic418967fa.accept_17_9_13_16_1_3266 43 81
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 237 3 14 27 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 237
  (Polychromatic418967fa.accept_16_9_1_13_1_1850 41 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 237 3 13 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 38
  81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 237 3 12 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 237 (Polychromatic418967fa.accept_10_4_1_7_1_371 34 81 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 237 3 11 27 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 237
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 32 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 237 3 10 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 237
  (Polychromatic418967fa.accept_17_12_13_16_1_3226 29 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 81 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 81 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 237 3 9 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 26
  81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 237
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 81 237 3 8 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 81 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 237 (Polychromatic418967fa.accept_15_7_6_12_1_1614 22 81
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 237 3 7 27 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 237 3 6 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 81 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 81 237 3 5 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 81 237 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 81 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 237 3 4 27 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 237
  (Polychromatic418967fa.accept_20_11_1_17_1_5535 11 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 237 3 3 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 237 (Polychromatic418967fa.accept_18_8_9_3_1_2645 8 81 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 237
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 81 237 3 2 27 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 81 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 81 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 237 3 1 27 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 81 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 237 (Polychromatic418967fa.accept_18_1_9_3_1_2672 1 81 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 237
  (allA_succ_of_accept 79 80 237 (accept_3_4 79 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 237 (accept_3_4 76 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 237 (Polychromatic418967fa.accept_11_9_3_6_1_797 75 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 237 (accept_3_4 73 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 237 (accept_3_4 70 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 68 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 237 (accept_3_4 67 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 237 (accept_3_4 64 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 237 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 237
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 62 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 237 (accept_3_4 61 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 237 (accept_3_4 58 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 237 (Polychromatic418967fa.accept_13_5_2_3_1_1526 57 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 237 (accept_3_4 55 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 237 (accept_3_4 52 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 237 (accept_3_4 49 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 237 (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 237 (accept_3_4 46 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 237 (Polychromatic418967fa.accept_14_3_10_13_1_339 45 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 237 (accept_3_4 43 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 237 (accept_3_4 40 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 237 (accept_3_4 37 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 237 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 237 (accept_3_4 34 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 237 (accept_3_4 31 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 237 (accept_3_4 28 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 237 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 237
  (Polychromatic418967fa.accept_25_1_5_12_1_14160 26 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 80 237 (accept_3_4 25 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  80 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 237 (accept_3_4 22 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 237 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 237 (accept_3_4 19 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 237 (accept_3_4 16 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 237 (accept_3_4 13 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 237 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 237 (accept_3_4 10 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 237
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 237 (accept_3_4 7 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 80 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 237 (accept_3_4 4 80 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 237 (Polychromatic418967fa.accept_14_3_10_13_1_339 3 80 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 80
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 237 (accept_3_4 1 80 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 237
  (allA_succ_of_accept 78 79 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 237 (accept_3_5 77 79 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  75 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 237 (accept_3_5 74
  79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 79 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 237 (accept_3_5 71 79 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 69
  79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 237 (accept_3_5 68 79
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 79 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 237 (accept_3_5 65 79 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  63 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 237 (accept_3_5 62
  79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 237
  (Polychromatic418967fa.accept_15_1_4_12_1_2401 61 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 79 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 79 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 237 (accept_3_5 59 79 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 79 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 57
  79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 237 (accept_3_5 56 79
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 237 (Polychromatic418967fa.accept_9_1_7_3_1_41
  55 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 237 (accept_3_5 53 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 237 (accept_3_5 50 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 79 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 237
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 237 (accept_3_5 47 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 237 (accept_3_5 44 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 79 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 237 (accept_3_5 41 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 237 (accept_3_5 38 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 79 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 237 (accept_3_5 35 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 237 (accept_3_5 32 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 79 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 237 (accept_3_5 29 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 237 (accept_3_5 26 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 79 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 237 (accept_3_5 23 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 237 (Polychromatic418967fa.accept_22_21_13_17_1_7959 21 79 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 237 (accept_3_5 20 79 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 79 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 237 (accept_3_5 17 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 237 (accept_3_5 14 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 79 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 237
  (Polychromatic418967fa.accept_10_2_9_7_1_720 12 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 237 (accept_3_5 11 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 237 (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 237 (accept_3_5 8 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 237 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 79 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 237 (accept_3_5 5 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 79 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 237 (accept_3_5 2 79 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 79 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 237
  (allA_succ_of_accept 77 78 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 237 3 25 26 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 74 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 237 3 24 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 70 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 237 3 23 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 237 3 22 26 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 78 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 78 237 3 21 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 78 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 237 3 20 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 237 3 19 26 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 78 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 237 3 18 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 53
  78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 78 237 3 17 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 78 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 237 3 16 26 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 78 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 237 3 15 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 78 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 237 3 14 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 78 237 3 13 26 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 78 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 78 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 237 3 12 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 78 237 3 11 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 78 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 237 3 10 26 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 78 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 237 3 9 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 78 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 78 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 237 3 8 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 237 3 7 26 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 237 3 6 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 237 3 5 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 78 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 237 3 4 26 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 78 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 78 237 3 3 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 78 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 78 237 3 2 26 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 78 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 78 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 78 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 237 3 1 26 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 78 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 78 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 78 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 237
  (allA_succ_of_accept 76 77 237 (accept_3_4 76 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 237 (accept_3_4 73 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 237 (Polychromatic418967fa.accept_21_9_14_6_1_11308 72 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 71 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 237 (accept_3_4 70 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 237 (accept_3_4 67 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 237 (Polychromatic418967fa.accept_15_6_2_12_1_885 66 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 65 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 237 (accept_3_4 64 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 237 (accept_3_4 61 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 237
  (Polychromatic418967fa.accept_15_14_2_12_1_2472 59 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 237 (accept_3_4 58 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 237 (Polychromatic418967fa.accept_14_1_7_13_1_333 57 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 237 (accept_3_4 55 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 237 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 237 (accept_3_4 52 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 237 (accept_3_4 49 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 237 (Polychromatic418967fa.accept_13_9_12_3_1_907 48 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 237 (accept_3_4 46 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 237 (Polychromatic418967fa.accept_21_3_14_6_1_11325 45 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 237 (accept_3_4 43 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 237
  (Polychromatic418967fa.accept_13_2_12_3_1_415 41 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 237 (accept_3_4 40 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 237 (accept_3_4 37 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 237 (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 237 (accept_3_4 34 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 237 (accept_3_4 31 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 237 (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 237 (accept_3_4 28 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 237 (accept_3_4 25 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 237
  (Polychromatic418967fa.accept_17_6_9_16_1_4410 23 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 237 (accept_3_4 22 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 237 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 237 (accept_3_4 19 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 237 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 237 (accept_3_4 16 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 237 (accept_3_4 13 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 237 (Polychromatic418967fa.accept_19_12_1_9_1_10281 12 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 237 (accept_3_4 10 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 237 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 237 (accept_3_4 7 77 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 77 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 237
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 237 (accept_3_4 4 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  237 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 77 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 237 (accept_3_4 1 77 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 237 (allA_succ_of_accept 75 76 237 (Polychromatic418967fa.accept_13_10_11_3_1_1518 75 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 237 (accept_3_5 74 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 237
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 72 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 76 237 (accept_3_5 71 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  76 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 76 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 237 (accept_3_5 68 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 237
  (Polychromatic418967fa.accept_12_6_4_9_1_544 66 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 76 237 (accept_3_5 65 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  76 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 76 237 (Polychromatic418967fa.accept_10_3_6_7_1_2188 63 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 237 (accept_3_5 62 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 76 237 (accept_3_5 59 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  76 237 (Polychromatic418967fa.accept_15_13_1_12_1_1638 58 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 76 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 237 (accept_3_5 56 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 237
  (Polychromatic418967fa.accept_12_6_4_9_1_544 54 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 76 237 (accept_3_5 53 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  76 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 76 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 237 (accept_3_5 50 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 237
  (Polychromatic418967fa.accept_17_14_8_16_1_6863 48 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 76 237 (accept_3_5 47 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  76 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 76 237 (Polychromatic418967fa.accept_21_3_13_6_1_11322 45 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 237 (accept_3_5 44 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 76 237 (accept_3_5 41 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  76 237 (Polychromatic418967fa.accept_13_1_11_3_1_901 40 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 76 237 (Polychromatic418967fa.accept_20_19_16_17_1_5473 39 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 237 (accept_3_5 38 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 237
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 76 237 (accept_3_5 35 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  76 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 76 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 237 (accept_3_5 32 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 237
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 76 237 (accept_3_5 29 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  76 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 76 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 237 (accept_3_5 26 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 76 237 (accept_3_5 23 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  76 237 (Polychromatic418967fa.accept_25_22_1_12_1_14159 22 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 76 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 237 (accept_3_5 20 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 237
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 76 237 (accept_3_5 17 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  76 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 76 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 237 (accept_3_5 14 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 237
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 76 237 (accept_3_5 11 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  76 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 76 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 237 (accept_3_5 8 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 76 237 (accept_3_5 5 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76
  237 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 76 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 76 237 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 237 (accept_3_5 2 76 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 237 (allA_succ_of_accept
  74 75 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 73 75 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 237 3 24 25 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 71 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 237 3 23 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 68
  75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 237 3 22 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 65 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 237 3 21 25 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 237 3 20 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  59 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 237 3 19 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 237 (Polychromatic418967fa.accept_16_8_11_13_1_7265 56 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 237 3 18 25 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 237 (Polychromatic418967fa.accept_10_2_5_7_1_1124 52 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 237 3 17 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 237 3 16 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 237 (Polychromatic418967fa.accept_11_3_9_6_1_105 47 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 237 3 15 25 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 237
  (Polychromatic418967fa.accept_17_10_7_16_1_6841 44 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 237 3 14 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 41
  75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 237
  (Polychromatic418967fa.accept_16_8_11_13_1_7265 40 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 237 3 13 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 237 3 12 25 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 237 3 11 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 237 3 10 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 237 3 9 25 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 237 3 8 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 23 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 237 3 7 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 237 (Polychromatic418967fa.accept_13_7_10_3_1_1505 20 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 237 3 6 25 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 237 (Polychromatic418967fa.accept_19_16_18_9_1_3295 16 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 237 3 5 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 237
  (Polychromatic418967fa.accept_10_3_5_7_1_330 13 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 237 3 4 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 237 3 3 25 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 237 3 2 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 75 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 237 3 1 25 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 75 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 237 (allA_succ_of_accept
  73 74 237 (accept_3_4 73 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 237 (accept_3_4 70 74 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 68
  74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 237 (accept_3_4 67 74
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 74 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 237 (accept_3_4 64 74 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 237 (Polychromatic418967fa.accept_9_8_2_3_1_447 62
  74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 237 (accept_3_4 61 74
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 237
  (Polychromatic418967fa.accept_9_6_2_3_1_771 60 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 237 (accept_3_4 58 74 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 237 (Polychromatic418967fa.accept_13_5_9_3_1_870 57 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 237
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 56 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 74 237 (accept_3_4 55 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 74 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 74 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 74 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 74 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 237 (accept_3_4 52 74 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 51
  74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 237 (accept_3_4 49 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 237 (Polychromatic418967fa.accept_18_12_2_3_1_6414 48 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 237 (accept_3_4 46 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 74 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 237 (accept_3_4 43 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 237 (accept_3_4 40 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 237 (accept_3_4 37 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 237 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 237 (accept_3_4 34 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 74 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 237 (accept_3_4 31 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 237 (accept_3_4 28 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 237 (accept_3_4 25 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 237 (accept_3_4 22 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 74 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 237
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 237 (accept_3_4 19 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 237 (accept_3_4 16 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 237 (accept_3_4 13 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 237 (accept_3_4 10 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 74 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 237 (accept_3_4 7 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 237 (accept_3_4 4 74 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  74 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 237 (accept_3_4 1 74 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 237 (allA_succ_of_accept
  72 73 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 237 (accept_3_5 71 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 73 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 73 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 237 (accept_3_5 68 73 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 67
  73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 237
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 66 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 237 (accept_3_5 65 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 237 (accept_3_5 62 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 237 (accept_3_5 59 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 237 (Polychromatic418967fa.accept_13_5_8_3_1_1535 57 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 237 (accept_3_5 56 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 237
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 237 (accept_3_5 53 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 237 (accept_3_5 50 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 237
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 48 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 237 (accept_3_5 47 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 237 (accept_3_5 44 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 237 (accept_3_5 41 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 237 (accept_3_5 38 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 237 (accept_3_5 35 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 237 (accept_3_5 32 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 237 (accept_3_5 29 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 237 (accept_3_5 26 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 237 (accept_3_5 23 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 237 (Polychromatic418967fa.accept_16_5_9_13_1_3845 21 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 237 (accept_3_5 20 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 237 (Polychromatic418967fa.accept_17_2_5_16_1_1264 19 73
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 237 (accept_3_5 17 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 237 (accept_3_5 14 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 237 (accept_3_5 11 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 237 (accept_3_5 8 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 73 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 237 (accept_3_5 5 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 73 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 237 (accept_3_5 2 73 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 237 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 73 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 237 (allA_succ_of_accept 71
  72 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 237 (Polychromatic418967fa.accept_19_13_15_9_1_3293 70 72 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 237 3 23 24 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 237
  (Polychromatic418967fa.accept_16_4_8_13_1_1059 68 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 237 3 22 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 65
  72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 64 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 237 3 21 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 237 (Polychromatic418967fa.accept_13_10_7_3_1_3041 62 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 237 (Polychromatic418967fa.accept_13_9_7_3_1_1531 61 72 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 237 3 20 24 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 237 (Polychromatic418967fa.accept_21_16_9_6_1_8335 58 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 237 3 19 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 237 (Polychromatic418967fa.accept_13_4_7_3_1_92 56
  72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 237
  (Polychromatic418967fa.accept_10_5_2_7_1_345 55 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 237 3 18 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 72 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 237 3 17 24 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 72 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 237 3 16 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 237 (Polychromatic418967fa.accept_13_8_7_3_1_430 47
  72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 46 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 72 237 3 15 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 72 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 44 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 72 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 237 3 14 24 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 237
  (Polychromatic418967fa.accept_19_3_15_9_1_4576 41 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 72 237 (Polychromatic418967fa.accept_13_1_7_3_1_1503 40 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 237 3 13 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 38
  72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 237
  (Polychromatic418967fa.accept_13_11_7_3_1_894 37 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 237 3 12 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 72 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 72 237 3 11 24 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 72 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 72 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 237 3 10 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 29
  72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 237
  (Polychromatic418967fa.accept_16_12_8_13_1_6073 28 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 72 237 3 9 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 72 237 (Polychromatic418967fa.accept_20_6_12_17_1_8581 26 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 72 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 237 3 8 24 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 237
  (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 72 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 72 237 3 7 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 72 237 (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 72 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 237
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 237 3 6 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 72 237 (Polychromatic418967fa.accept_21_16_9_6_1_8335 16 72
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 237 3 5 24 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 237
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 72 237 (Polychromatic418967fa.accept_19_13_15_9_1_3293 13 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 237 3 4 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 72 237 3 3 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 72 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 237 (Polychromatic418967fa.accept_20_7_12_17_1_8580 7 72 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 237 3 2 24 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 237
  (Polychromatic418967fa.accept_10_5_2_7_1_345 5 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 72 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 72 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 72 237 3 1 24 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 72 237 (Polychromatic418967fa.accept_19_2_15_9_1_7318 2 72 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 72 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 237
  (allA_succ_of_accept 70 71 237 (accept_3_4 70 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 237 (accept_3_4 67 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 237 (accept_3_4 64 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 237 (accept_3_4 61 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 59 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 237 (accept_3_4 58 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 237 (Polychromatic418967fa.accept_13_5_6_3_1_868 57 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 237 (accept_3_4 55 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 237
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 53 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 237 (accept_3_4 52 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 237 (accept_3_4 49 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 237 (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 237 (accept_3_4 46 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 237 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 237 (accept_3_4 43 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 237 (accept_3_4 40 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 237 (accept_3_4 37 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 237 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 237
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 237 (accept_3_4 34 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 237 (accept_3_4 31 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 237 (accept_3_4 28 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 237 (accept_3_4 25 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 237 (accept_3_4 22 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 237 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 237 (accept_3_4 19 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 237
  (Polychromatic418967fa.accept_19_17_14_9_1_8833 17 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 237 (accept_3_4 16 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 237 (accept_3_4 13 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 237 (accept_3_4 10 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 237 (accept_3_4 7 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 237 (accept_3_4 4 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  237 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 71 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 237 (accept_3_4 1 71 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 237 (allA_succ_of_accept 69 70 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 237 (accept_3_5 68 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 237
  (Polychromatic418967fa.accept_12_6_10_9_1_531 66 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 70 237 (accept_3_5 65 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  70 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 237 (accept_3_5 62 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 70 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 70 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 60 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 70 237 (accept_3_5 59 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  70 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 70 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 70 237 (accept_3_5 56 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 70 237
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 70 237 (accept_3_5 53 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  70 237 (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 70 237 (accept_3_5 50 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 70 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 70 237
  (Polychromatic418967fa.accept_13_9_5_3_1_428 48 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 70 237 (accept_3_5 47 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  70 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 70 237 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 237 (accept_3_5 44 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 237 (accept_3_5 41 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  70 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 237 (accept_3_5 38 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 70 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 237
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 70 237 (accept_3_5 35 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  70 237 (Polychromatic418967fa.accept_13_8_5_3_1_427 34 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 70 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 237 (accept_3_5 32 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 237
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 70 237 (accept_3_5 29 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  70 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 70 237 (accept_3_5 26 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 70 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 70 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 70 237 (accept_3_5 23 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  70 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 70 237 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 70 237 (accept_3_5 20 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 237
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 237 (accept_3_5 17 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 237 (Polychromatic418967fa.accept_21_16_7_6_1_6687 16 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 70 237 (accept_3_5 14 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 237
  (Polychromatic418967fa.accept_21_12_7_6_1_3607 12 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 237 (accept_3_5 11 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  70 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 70 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 237 (accept_3_5 8 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 70 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 70 237 (accept_3_5 5 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70
  237 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 70 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 70 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 70 237 (accept_3_5 2 70 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 70 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 237 (allA_succ_of_accept 68 69
  237 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 237 3 22 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 65
  69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 69 237 3 21 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 69 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 62 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 69 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 69 237 3 20 23 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 69 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 237 3 19 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 55 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 69 237 3 18 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 69 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 69 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 237 3 17 23 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 50 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 237 3 16 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 47
  69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 69 237 3 15 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 69 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 44 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 69 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 237 3 14 23 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 69 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 237 3 13 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 38
  69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 69 237 3 12 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 69 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 69 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 237 3 11 23 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 237 3 10 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 69 237 3 9 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 69 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 69 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 69 237 3 8 23 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 69 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 237 3 7 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 69 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 69 237 3 6 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 69 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 69 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 69 237 3 5 23 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 69 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 237 3 4 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 69 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 69 237 3 3 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 69 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 69 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 69 237 3 2 23 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 69 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 69 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 237 3 1 23 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 69 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 69 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 69 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 237
  (allA_succ_of_accept 67 68 237 (accept_3_4 67 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  68 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 237 (accept_3_4 64 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 237 (Polychromatic418967fa.accept_15_3_8_12_1_900 63 68 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 62 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 237 (accept_3_4 61 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 237 (accept_3_4 58 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 68 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 237 (accept_3_4 55 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 237 (accept_3_4 52 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 68 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 237 (accept_3_4 49 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 237 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 237 (accept_3_4 46 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 237 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 68 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 44 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 237 (accept_3_4 43 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 237 (accept_3_4 40 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 68 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 237 (accept_3_4 37 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 237 (accept_3_4 34 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 68 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 237 (accept_3_4 31 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 237 (accept_3_4 28 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 237 (Polychromatic418967fa.accept_18_9_14_3_1_6407 27 68 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 237 (accept_3_4 25 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 237 (accept_3_4 22 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 237 (Polychromatic418967fa.accept_19_2_11_9_1_1119 21 68 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 237 (accept_3_4 19 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 237 (accept_3_4 16 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 68 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 237
  (Polychromatic418967fa.accept_19_14_11_9_1_3330 14 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 237 (accept_3_4 13 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 237 (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 237 (accept_3_4 10 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 68 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 237 (accept_3_4 7 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 68 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 237 (accept_3_4 4 68 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 237 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 68 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 68
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 237 (accept_3_4 1 68 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 237 (allA_succ_of_accept 66 67
  237 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 237 (accept_3_5 65 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 237 (accept_3_5 62 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 67 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 237 (accept_3_5 59 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 237 (Polychromatic418967fa.accept_13_5_2_3_1_1526 57 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 237 (accept_3_5 56 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 67 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 237 (accept_3_5 53 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 237 (accept_3_5 50 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 237 (Polychromatic418967fa.accept_11_5_1_6_1_774 49 67 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 237
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 237 (accept_3_5 47 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 237 (accept_3_5 44 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 67 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 237 (accept_3_5 41 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 237 (accept_3_5 38 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 67 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 237
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 237 (accept_3_5 35 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 237 (accept_3_5 32 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 67 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 237 (accept_3_5 29 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 237 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 237 (accept_3_5 26 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 67 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 237 (accept_3_5 23 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 237 (Polychromatic418967fa.accept_15_6_7_12_1_869 21 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 237 (accept_3_5 20 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 67 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 237 (accept_3_5 17 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 237 (accept_3_5 14 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 237 (Polychromatic418967fa.accept_19_13_10_9_1_5995 13 67 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 237 (accept_3_5 11 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 237 (accept_3_5 8 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 67 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 237 (accept_3_5 5 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 67 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 237 (accept_3_5 2 67 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 67 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 237 (allA_succ_of_accept 65 66
  237 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 66 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 64 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 237 3 21 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 62
  66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 66 237
  (Polychromatic418967fa.accept_10_1_6_7_1_710 61 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 66 237 3 20 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 66 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 66 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 66 237 3 19 22 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 66 237
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 66 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 237 3 18 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 53
  66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 237
  (Polychromatic418967fa.accept_12_4_6_9_1_548 52 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 66 237 3 17 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 66 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 237 (Polychromatic418967fa.accept_18_13_12_3_1_3857 49 66
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 237 3 16 22 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 66 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 237 3 15 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 66
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 66 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 66 237 3 14 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 66 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 41 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 66 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 66 237 3 13 22 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 66 237
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 66 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 237 3 12 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 237
  (Polychromatic418967fa.accept_12_10_6_9_1_549 34 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 66 237 3 11 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 66 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 237 3 10 22 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 237
  (Polychromatic418967fa.accept_20_9_6_17_1_1654 29 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 66 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 237 3 9 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 66 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 66 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 66 237 3 8 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 66 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 66 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 66 237 3 7 22 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 66 237
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 66 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 237 3 6 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 237 (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 66 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 16 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 66 237 3 5 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 66 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 237 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 66 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 237 3 4 22 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 66 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 237 3 3 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 66 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 237 3 2 22 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 237 (Polychromatic418967fa.accept_13_5_1_3_1_878 5 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 66 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 66 237 3 1 22 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 66 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 66 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 66 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 66 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 237 (allA_succ_of_accept 64 65 237 (accept_3_4 64 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 63 65 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 65 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 237 (accept_3_4 61 65 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 60
  65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 237 (accept_3_4 58 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 237 (accept_3_4 55 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 237 (Polychromatic418967fa.accept_15_9_5_12_1_1640 54 65 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 237 (accept_3_4 52 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 237 (accept_3_4 49 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 65 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 237
  (Polychromatic418967fa.accept_15_2_5_12_1_369 47 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 237 (accept_3_4 46 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 237 (accept_3_4 43 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 65 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 237 (accept_3_4 40 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 237 (accept_3_4 37 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 237 (accept_3_4 34 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 237 (accept_3_4 31 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 237 (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 65 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 237 (accept_3_4 28 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 237 (accept_3_4 25 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 237 (accept_3_4 22 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 237 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 237 (accept_3_4 19 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 65 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 237 (accept_3_4 16 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 237 (accept_3_4 13 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 65 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 237 (accept_3_4 10 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 237 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 237 (accept_3_4 7 65 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 65 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 237 (accept_3_4 4 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  237 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 65 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 237 (accept_3_4 1 65 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 237
  (allA_succ_of_accept 63 64 237 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 237 (accept_3_5 62 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 60
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 237 (accept_3_5 59 64
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 58 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 64 237 (Polychromatic418967fa.accept_21_15_1_6_1_8258 57 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 237 (accept_3_5 56 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 64 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 54
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 237 (accept_3_5 53 64
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 237
  (Polychromatic418967fa.accept_9_7_1_3_1_443 52 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 64 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 237 (accept_3_5 50 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 64 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 237 (Polychromatic418967fa.accept_13_9_12_3_1_907
  48 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 237 (accept_3_5 47
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 237
  (Polychromatic418967fa.accept_15_1_4_12_1_2401 46 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 64 237 (Polychromatic418967fa.accept_21_3_1_6_1_1162 45 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 237 (accept_3_5 44 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 64 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 42
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 237 (accept_3_5 41 64
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 40 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 64 237 (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 237 (accept_3_5 38 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 64 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 237 (Polychromatic418967fa.accept_11_3_9_6_1_105
  36 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 237 (accept_3_5 35
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 237
  (Polychromatic418967fa.accept_9_7_1_3_1_443 34 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 64 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 237 (accept_3_5 32 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 64 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 30
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 237 (accept_3_5 29 64
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 237
  (Polychromatic418967fa.accept_13_2_12_3_1_415 28 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 64 237 (Polychromatic418967fa.accept_19_8_7_9_1_10251 27 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 237 (accept_3_5 26 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 64 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 24
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 237 (accept_3_5 23 64
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 22 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 64 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 237 (accept_3_5 20 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 64 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 237 (Polychromatic418967fa.accept_12_6_4_9_1_544
  18 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 237 (accept_3_5 17
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 64 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 237 (accept_3_5 14 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 64 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 237 (accept_3_5 11 64
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 237
  (Polychromatic418967fa.accept_19_10_7_9_1_10345 10 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 64 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 237 (accept_3_5 8 64 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 64 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 237 (accept_3_5 5 64 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 4
  64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 237
  (Polychromatic418967fa.accept_10_3_4_7_1_353 3 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 64 237 (accept_3_5 2 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64
  237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 237
  (allA_succ_of_accept 62 63 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 63 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 237 3 20 21 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 63 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 237 3 19 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 63 237 (Polychromatic418967fa.accept_10_6_3_7_1_2197
  56 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 237
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 63 237 3 18 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 63 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 53 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 237 (Polychromatic418967fa.accept_15_7_3_12_1_365 52 63 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 237 3 17 21 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 237 3 16 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 237 (Polychromatic418967fa.accept_11_3_8_6_1_788 47
  63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 63 237 3 15 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 237 (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 63 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 237 3 14 21 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 237 (Polychromatic418967fa.accept_13_1_11_3_1_901 40 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 237 3 13 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 237 3 12 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 63 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 237 3 11 21 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 237
  (Polychromatic418967fa.accept_15_2_3_12_1_891 32 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 237 3 10 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 29
  63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 237
  (Polychromatic418967fa.accept_13_2_11_3_1_873 28 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 63 237 3 9 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 63 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 237 3 8 21 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 237 3 7 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 237 (Polychromatic418967fa.accept_13_7_11_3_1_1540 20 63 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 237 3 6 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 237 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 63 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 237 3 5 21 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 237 3 4 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 237 3 3 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 237 (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 63 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 237 3 2 21 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 237
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 237 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 63 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 237 3 1 21 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 63 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 237 (allA_succ_of_accept
  61 62 237 (accept_3_4 61 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 237
  (Polychromatic418967fa.accept_9_6_8_3_1_183 60 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 237 (accept_3_4 58 62 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 237 (Polychromatic418967fa.accept_21_15_20_6_1_6625 57 62 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 62 237 (accept_3_4 55 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  62 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 54 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 62 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 237 (accept_3_4 52 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 62 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 62 237 (accept_3_4 49 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  62 237 (Polychromatic418967fa.accept_15_3_2_12_1_2469 48 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 62 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 237 (accept_3_4 46 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 62 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 62 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 237
  (Polychromatic418967fa.accept_10_4_2_7_1_373 44 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 62 237 (accept_3_4 43 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  62 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 62 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 237 (accept_3_4 40 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 62 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 62 237 (accept_3_4 37 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  62 237 (Polychromatic418967fa.accept_15_6_2_12_1_885 36 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 62 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 237 (accept_3_4 34 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 62 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 62 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 62 237 (accept_3_4 31 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  62 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 62 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 237 (accept_3_4 28 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 62 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 237
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 237 (accept_3_4 25 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 237 (accept_3_4 22 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 237 (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 62 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 237
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 237 (accept_3_4 19 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 237 (accept_3_4 16 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 237
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 237 (accept_3_4 13 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 237 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 237 (accept_3_4 10 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 237 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 62 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 237
  (Polychromatic418967fa.accept_24_8_14_21_1_10947 8 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 237 (accept_3_4 7 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 237 (accept_3_4 4 62 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  62 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 237 (accept_3_4 1 62 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 237 (allA_succ_of_accept 60 61 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 237 (accept_3_5 59 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 237 (accept_3_5 56 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 61 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 237
  (Polychromatic418967fa.accept_10_4_1_7_1_371 54 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 237 (accept_3_5 53 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 237 (accept_3_5 50 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 61 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 237
  (Polychromatic418967fa.accept_14_6_5_13_1_367 48 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 237 (accept_3_5 47 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 237 (Polychromatic418967fa.accept_13_6_9_3_1_915 45 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 237 (accept_3_5 44 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 61 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 237 (accept_3_5 41 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 237 (accept_3_5 38 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 61 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 237 (accept_3_5 35 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 237 (accept_3_5 32 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 61 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 237
  (Polychromatic418967fa.accept_18_12_7_3_1_2666 30 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 237 (accept_3_5 29 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 237 (accept_3_5 26 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 61 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 237 (accept_3_5 23 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 237 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 237 (accept_3_5 20 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 61 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 237 (accept_3_5 17 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 237 (accept_3_5 14 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 61 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 237
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 237 (accept_3_5 11 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 237 (Polychromatic418967fa.accept_17_9_10_16_1_3217 9 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 237 (accept_3_5 8 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 237 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 61 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 237 (accept_3_5 5 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 61 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 237 (accept_3_5 2 61 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 61 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 237 (allA_succ_of_accept 59 60 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 58 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 237 3 19 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 60 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 237 3 18 20 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 237 3 17 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 50
  60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 237 3 16 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 60 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 237 3 15 20 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 237 3 14 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 41
  60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 60 237 3 13 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 60 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 237 3 12 20 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 237 3 11 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 237 3 10 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 60 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 237 3 9 20 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 60 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 237 3 8 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 60 237 3 7 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 60 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 60 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 237 3 6 20 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 237 3 5 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 60 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 237 3 4 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 60 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 237 3 3 20 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 237 3 2 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 60 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 60 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 60 237 3 1 20 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 60 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 60 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 60 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 237 (allA_succ_of_accept 58 59 237
  (accept_3_4 58 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 237
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 237 (accept_3_4 55 59 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 53
  59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 237 (accept_3_4 52 59
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 237 (Polychromatic418967fa.accept_7_2_3_6_1_4
  51 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 59 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 59 237 (accept_3_4 49 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  59 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 59 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 59 237 (accept_3_4 46 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 59 237 (Polychromatic418967fa.accept_19_7_2_9_1_6006 45 59 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 59 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 59 237 (accept_3_4 43 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  59 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 59 237 (Polychromatic418967fa.accept_15_11_14_12_1_2458 41 59 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 59 237 (accept_3_4 40 59 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 59 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 59 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 59 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 59 237 (accept_3_4 37 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  59 237 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 59 237 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 59 237 (accept_3_4 34 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 59 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 59 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 59 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 59 237 (accept_3_4 31 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  59 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 59 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 59 237 (accept_3_4 28 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 59 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 59 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 59 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 59 237 (accept_3_4 25 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  59 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 59 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 59 237 (accept_3_4 22 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 59 237 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 59 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 59 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 59 237 (accept_3_4 19 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  59 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 59 237 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 59 237 (accept_3_4 16 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 59 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 59 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 59 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 59 237 (accept_3_4 13 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  59 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 59 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 59 237 (accept_3_4 10 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 59 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 59 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 59 237 (accept_3_4 7 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59
  237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 59 237 (Polychromatic418967fa.accept_25_5_9_12_1_14158 5 59 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 237 (accept_3_4 4 59 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 59 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 59 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 237 (accept_3_4 1 59 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59 237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 58 237 (allA_succ_of_accept 57 58 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 58 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 237 (accept_3_5 56 58 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 58 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 237
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 58 237 (accept_3_5 53 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  58 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 58 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 237 (accept_3_5 50 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 58 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 58 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 237
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 237 (accept_3_5 47 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 237 (accept_3_5 44 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 237 (accept_3_5 41 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 237 (Polychromatic418967fa.accept_13_1_6_3_1_1547 40 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 237 (accept_3_5 38 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 237 (accept_3_5 35 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 237 (accept_3_5 32 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 237
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 237 (accept_3_5 29 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 237 (accept_3_5 26 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 58 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 237 (accept_3_5 23 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 237 (Polychromatic418967fa.accept_16_5_10_13_1_6042 21 58 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 237 (accept_3_5 20 58 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 237 (accept_3_5 17 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 237 (accept_3_5 14 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 237
  (Polychromatic418967fa.accept_16_12_10_13_1_1042 12 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 58 237 (accept_3_5 11 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 58 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 58 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 58 237 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 58 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 237 (accept_3_5 8 58 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 237 (accept_3_5 5 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  237 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 58 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 237 (accept_3_5 2 58 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 237 (allA_succ_of_accept 56 57 237 (Polychromatic418967fa.accept_22_12_13_17_1_14157 56 57 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 237
  (Polychromatic418967fa.accept_16_7_9_13_1_4948 55 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 57 237 3 18 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 57 237 (Polychromatic418967fa.accept_13_1_5_3_1_888 53 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 52 57 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 237 3 17 19 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 237
  (Polychromatic418967fa.accept_13_11_5_3_1_889 50 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 237 (Polychromatic418967fa.accept_14_7_1_13_1_357 49 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 237 3 16 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 47
  57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 237
  (Polychromatic418967fa.accept_21_4_15_6_1_8327 46 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 57 237 3 15 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 57 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 237 (Polychromatic418967fa.accept_17_9_6_16_1_3280 43 57
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 237 3 14 19 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 237
  (Polychromatic418967fa.accept_13_2_5_3_1_406 41 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 57 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 237 3 13 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 237 (Polychromatic418967fa.accept_16_6_9_13_1_2751
  38 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 57 237 3 12 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 57 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 35 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 237 (Polychromatic418967fa.accept_13_8_5_3_1_427 34 57 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 237 3 11 19 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 237
  (Polychromatic418967fa.accept_13_6_5_3_1_426 32 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 237 (Polychromatic418967fa.accept_21_10_15_6_1_5090 31 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 237 3 10 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 237 (Polychromatic418967fa.accept_21_8_15_6_1_8247
  29 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 237
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 57 237 3 9 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 57 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 237 (Polychromatic418967fa.accept_21_4_15_6_1_8327 25 57
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 237 3 8 19 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 57 237 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 237 3 7 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 57 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 57 237 3 6 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 57 237 (Polychromatic418967fa.accept_16_1_9_13_1_1822 17 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 57 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 237 3 5 19 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 237
  (Polychromatic418967fa.accept_13_1_5_3_1_888 14 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 237 (Polychromatic418967fa.accept_21_13_15_6_1_3556 13 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 237 3 4 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 237 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 57 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 237
  (Polychromatic418967fa.accept_17_10_6_16_1_6862 10 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 57 237 3 3 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 57 237 (Polychromatic418967fa.accept_13_8_5_3_1_427 8 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 237 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 57 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 237 3 2 19 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 57 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 57 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 57 237 3 1 19 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 57 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 57 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 237
  (Polychromatic418967fa.accept_13_1_5_3_1_888 1 57 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 57 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 237 (allA_succ_of_accept 55 56
  237 (accept_3_4 55 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 56 237
  (Polychromatic418967fa.accept_12_6_8_9_1_553 54 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 56 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 237 (accept_3_4 52 56 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 56 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 50
  56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 56 237 (accept_3_4 49 56
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 56 237
  (Polychromatic418967fa.accept_18_12_2_3_1_6414 48 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 56 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 237 (accept_3_4 46 56 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 56 237 (Polychromatic418967fa.accept_17_11_5_16_1_5600 45 56 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 56 237 (accept_3_4 43 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  56 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 56 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 56 237 (accept_3_4 40 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 56 237 (Polychromatic418967fa.accept_20_19_16_17_1_5473 39 56 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 56 237
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 56 237 (accept_3_4 37 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  56 237 (Polychromatic418967fa.accept_16_4_8_13_1_1059 36 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 56 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 56 237 (accept_3_4 34 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 56 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 237 (accept_3_4 31 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 56 237 (accept_3_4 28 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 56 237 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 56 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 237 (accept_3_4 25 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 237 (accept_3_4 22 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 56 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 56 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 56 237
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 20 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 56 237 (accept_3_4 19 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  56 237 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 56 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 56 237 (accept_3_4 16 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 56 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 56 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 56 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 56 237 (accept_3_4 13 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  56 237 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 56 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 237 (accept_3_4 10 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 237 (Polychromatic418967fa.accept_18_9_2_3_1_5082 9 56 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 56 237 (accept_3_4 7 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 56
  237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 56 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 237 (accept_3_4 4 56 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 56 237 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 56 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 237 (Polychromatic418967fa.accept_17_2_5_16_1_1264
  2 56 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 56 237 (accept_3_4 1 56
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 237))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 237 (allA_succ_of_accept 54 55 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 55 237 (accept_3_5 53 55 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 55 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 55 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 55 237 (accept_3_5 50 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  55 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 55 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 237 (accept_3_5 47 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 55 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 55 237
  (Polychromatic418967fa.accept_18_9_1_3_1_6451 45 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 55 237 (accept_3_5 44 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  55 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 55 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 55 237 (accept_3_5 41 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 55 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 55 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 55 237 (accept_3_5 38 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  55 237 (Polychromatic418967fa.accept_15_7_10_12_1_2403 37 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 55 237 (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 55 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 55 237 (accept_3_5 35 55 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 55 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 55 237 (accept_3_5 32 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  55 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 55 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 55 237 (accept_3_5 29 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 237
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 237 (accept_3_5 26 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  55 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 55 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 55 237 (accept_3_5 23 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 55 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 237
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 55 237 (accept_3_5 20 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  55 237 (Polychromatic418967fa.accept_20_19_15_17_1_7059 19 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 55 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 237 (accept_3_5 17 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 55 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 55 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 55 237 (accept_3_5 14 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  55 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 55 237 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 55 237 (accept_3_5 11 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 55 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 55 237
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 55 237 (accept_3_5 8 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 55
  237 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 55 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 55 237 (accept_3_5 5 55 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 55 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 55 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 3
  55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 237 (accept_3_5 2 55 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 237 (Polychromatic418967fa.accept_19_1_17_9_1_2150
  1 55 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 237 (allA_succ_of_accept 53 54 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 54 237 3 17 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 54 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 50
  54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 237
  (Polychromatic418967fa.accept_11_5_10_6_1_793 49 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 54 237 3 16 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 54 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 54 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 54 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 237 3 15 18 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 237
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 54 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 237 3 14 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 41
  54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 237
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 54 237 3 13 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 54 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 38 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 237 (Polychromatic418967fa.accept_13_11_2_3_1_883 37 54 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 237 3 12 18 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 54 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 54 237 3 11 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 54 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 54 237 3 10 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 54 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 54 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 54 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 237 3 9 18 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 237
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 54 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 237 3 8 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 54 237 3 7 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 54 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 237 3 6 18 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 237
  (Polychromatic418967fa.accept_21_17_12_6_1_12761 17 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 54 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 16 54 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 54 237 3 5 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 54 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 237
  (Polychromatic418967fa.accept_10_3_4_7_1_353 13 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 237 3 4 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 54 237 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 54 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 237 3 3 18 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 54 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 237 3 2 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 54 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 54 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 54 237 3 1 18 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 54 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 54 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 54 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  237)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 237 (allA_succ_of_accept 52 53 237 (accept_3_4
  52 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 237 (accept_3_4 49 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 237 (Polychromatic418967fa.accept_15_3_8_12_1_900 48 53 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 237 (accept_3_4 46 53
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 237 (accept_3_4 43 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 53 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 41
  53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 237 (accept_3_4 40 53
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 237
  (Polychromatic418967fa.accept_12_3_5_9_1_176 39 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 53 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 237 (accept_3_4 37 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 53 237 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 53 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108
  35 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 237 (accept_3_4 34
  53 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 53 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 237 (accept_3_4 31 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 53 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 53 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 29
  53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 237 (accept_3_4 28 53
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 237
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 53 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 237 (accept_3_4 25 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 53 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 23
  53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 237 (accept_3_4 22 53
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 237
  (Polychromatic418967fa.accept_19_2_15_9_1_7318 21 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 53 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 237 (accept_3_4 19 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 53 237 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 53 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 237 (accept_3_4 16 53
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 237
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 53 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 237 (accept_3_4 13 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 53 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 11
  53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 237 (accept_3_4 10 53
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 237 (Polychromatic418967fa.accept_7_2_4_6_1_166
  9 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 237 (accept_3_4 7 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 53 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 237 (accept_3_4 4 53 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 53 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 237 (accept_3_4 1 53 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 237)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 237 (allA_succ_of_accept 51 52 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 52 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 237 (accept_3_5 50 52 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 237
  (Polychromatic418967fa.accept_15_3_7_12_1_372 48 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 237 (accept_3_5 47 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 237 (accept_3_5 44 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 52 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 237 (accept_3_5 41 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 237 (accept_3_5 38 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 237
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 237 (accept_3_5 35 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 237 (accept_3_5 32 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 237 (accept_3_5 29 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 237 (Polychromatic418967fa.accept_19_8_14_9_1_4590 27 52 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 237 (accept_3_5 26 52 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 237 (accept_3_5 23 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 237 (Polychromatic418967fa.accept_15_6_7_12_1_869 21 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 237 (accept_3_5 20 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 237 (accept_3_5 17 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 237 (accept_3_5 14 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 52 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 237
  (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 237 (accept_3_5 11 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 237 (accept_3_5 8 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 237 (accept_3_5 5 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  237 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 52 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 237 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 52 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 237 (accept_3_5 2 52 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 237))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 237 (allA_succ_of_accept 50 51 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 51 237 3 16 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 51 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 237 3 15 17 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 237 3 14 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 51 237 3 13 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 51 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 51 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 237 3 12 17 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 237 3 11 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 32
  51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 237 3 10 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 51 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 237 3 9 17 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 237 3 8 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 51 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 237 3 7 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 51 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 237 3 6 17 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 237 3 5 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 237 3 4 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 237 3 3 17 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 237 3 2 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 51 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 51 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 237 3 1 17 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 51 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  237))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 237 (allA_succ_of_accept 49 50 237 (accept_3_4 49
  50 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 237
  (Polychromatic418967fa.accept_18_12_14_3_1_2655 48 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 237 (accept_3_4 46 50 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 237 (Polychromatic418967fa.accept_18_9_14_3_1_6407 45 50 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 237 (accept_3_4 43 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 237 (accept_3_4 40 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 237 (accept_3_4 37 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 237 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 237 (accept_3_4 34 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 50 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 237
  (Polychromatic418967fa.accept_15_2_5_12_1_369 32 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 237 (accept_3_4 31 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 237 (accept_3_4 28 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 237 (accept_3_4 25 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 237 (accept_3_4 22 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 237 (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 50 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 237 (accept_3_4 19 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 237 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 237 (accept_3_4 16 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 237
  (Polychromatic418967fa.accept_13_1_11_3_1_901 14 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 237 (accept_3_4 13 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 237 (accept_3_4 10 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 50 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 237 (accept_3_4 7 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 50 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 237 (accept_3_4 4 50 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  50 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 237 (accept_3_4 1 50 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 237)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 237 (allA_succ_of_accept 48 49 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 237 (accept_3_5 47 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 237
  (Polychromatic418967fa.accept_11_1_5_6_1_397 45 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 237 (accept_3_5 44 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 237 (accept_3_5 41 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 237
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 237 (accept_3_5 38 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 237 (accept_3_5 35 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 49 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 237 (accept_3_5 32 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 237 (Polychromatic418967fa.accept_15_1_4_12_1_2401 31 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 237 (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 49 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 237 (accept_3_5 29 49 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 49 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 237
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 237 (accept_3_5 26 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 237 (accept_3_5 23 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 49 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 237
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 237 (accept_3_5 20 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 237 (accept_3_5 17 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 237 (accept_3_5 14 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 237 (Polychromatic418967fa.accept_21_13_7_6_1_3656 13 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 237 (accept_3_5 11 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 49 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 237
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 237 (accept_3_5 8 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  237 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 49 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 237 (accept_3_5 5 49 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 3
  49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 237 (accept_3_5 2 49 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  49 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  237))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 237 (allA_succ_of_accept 47 48 237
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 47 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 48 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 46 48 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 237 3 15 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 237 (Polychromatic418967fa.accept_13_5_9_3_1_870 44
  48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 48 237
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 237 3 14 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 237 (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 48 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 237 (Polychromatic418967fa.accept_14_12_6_13_1_3173 40 48
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 48 237 3 13 16 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 48 237
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 38 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 48 237 (Polychromatic418967fa.accept_15_7_3_12_1_365 37 48 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 237 3 12 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 237 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  35 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 237
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 34 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 48 237 3 11 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 48 237 (Polychromatic418967fa.accept_13_6_9_3_1_915 32 48 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 48 237 (Polychromatic418967fa.accept_13_5_9_3_1_870 31 48 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 237 3 10 16 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 237
  (Polychromatic418967fa.accept_10_9_8_7_1_714 29 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 237 (Polychromatic418967fa.accept_13_2_9_3_1_2212 28 48 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 48 237 3 9 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 48 237 (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 48
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 237
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 237 3 8 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 237 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 48 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 48 237 (Polychromatic418967fa.accept_15_7_3_12_1_365 22 48 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 237 3 7 16 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 237
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 48 237 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 48 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 237 3 6 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 237 (Polychromatic418967fa.accept_15_2_3_12_1_891 17 48 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 237
  (Polychromatic418967fa.accept_19_16_10_9_1_8842 16 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 48 237 3 5 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 48 237 (Polychromatic418967fa.accept_18_14_12_3_1_5103 14 48 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 48 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 237 3 4 16 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 237
  (Polychromatic418967fa.accept_17_11_14_16_1_1270 11 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 48 237 (Polychromatic418967fa.accept_20_10_8_17_1_12900 10 48 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 48 237 3 3 16 79 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 48 237
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 48 237 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 48 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 237 3 2 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 237 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 48 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48 237
  (Polychromatic418967fa.accept_19_4_10_9_1_4569 4 48 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 48 237 3 1 16 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 48 237 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 48 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 237 (Polychromatic418967fa.accept_18_1_12_3_1_6426 1 48 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  237)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 237 (allA_succ_of_accept 46 47 237 (accept_3_4 46 47
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 237
  (Polychromatic418967fa.accept_21_3_5_6_1_14156 45 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 237 (accept_3_4 43 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 41
  47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 237 (accept_3_4 40 47
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 237 (accept_3_4 37 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 237 (Polychromatic418967fa.accept_9_8_2_3_1_447 35
  47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 237 (accept_3_4 34 47
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 237
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 237 (accept_3_4 31 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 237 (accept_3_4 28 47
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 237
  (Polychromatic418967fa.accept_12_3_11_9_1_193 27 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 237 (accept_3_4 25 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 47 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 23
  47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 237 (accept_3_4 22 47
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 237
  (Polychromatic418967fa.accept_15_6_2_12_1_885 21 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 237 (accept_3_4 19 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 237 (Polychromatic418967fa.accept_9_8_2_3_1_447 17
  47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 237 (accept_3_4 16 47
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 237 (Polychromatic418967fa.accept_7_1_5_6_1_59
  15 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 237 (accept_3_4 13 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 237 (Polychromatic418967fa.accept_16_12_15_13_1_3872 12 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 237 (accept_3_4 10 47 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 237 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 47 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 237 (accept_3_4 7 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 47 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 237 (accept_3_4 4 47 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 47 237 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 47 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 237 (accept_3_4 1 47 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47 237))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46
  237 (allA_succ_of_accept 45 46 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 237 (accept_3_5 44 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 46 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 42
  46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 237 (accept_3_5 41 46
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 237 (accept_3_5 38 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 237 (Polychromatic418967fa.accept_13_10_7_3_1_3041
  36 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 237 (accept_3_5 35
  46 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 237
  (Polychromatic418967fa.accept_9_7_1_3_1_443 34 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 46 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 237 (accept_3_5 32 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 46 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 30
  46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 237 (accept_3_5 29 46
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 237
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 28 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 237 (accept_3_5 26 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24
  46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 237 (accept_3_5 23 46
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 237
  (Polychromatic418967fa.accept_9_4_1_3_1_190 22 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 237 (accept_3_5 20 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 237 (Polychromatic418967fa.accept_12_6_10_9_1_531
  18 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 237 (accept_3_5 17
  46 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 46 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 237 (accept_3_5 14 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 46 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12
  46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 237 (accept_3_5 11 46
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 10 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 46 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 237 (accept_3_5 8 46 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 46 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 237 (accept_3_5 5 46 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 4
  46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 237 (accept_3_5 2 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46
  237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 237)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 237 (allA_succ_of_accept 44 45 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 45 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 237 3 14 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 237 (Polychromatic418967fa.accept_21_20_3_6_1_8291
  41 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 237
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 40 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 237 3 13 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 38 45 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 45 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 237 3 12 15 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 237
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 237 (Polychromatic418967fa.accept_21_13_3_6_1_8232 34 45 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 237 3 11 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 32
  45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 237
  (Polychromatic418967fa.accept_13_5_6_3_1_868 31 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 237 3 10 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 237 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 45 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 45 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 237 3 9 15 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 237
  (Polychromatic418967fa.accept_18_8_9_3_1_2645 26 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 45 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 237 3 8 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 45 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 237
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 22 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 237 3 7 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 237 (Polychromatic418967fa.accept_18_2_9_3_1_3825 20 45 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 237 (Polychromatic418967fa.accept_18_1_9_3_1_2672 19 45 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 237 3 6 15 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 237
  (Polychromatic418967fa.accept_19_17_7_9_1_3324 17 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 45 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 237 3 5 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 237 (Polychromatic418967fa.accept_13_1_6_3_1_1547 14 45 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 237
  (Polychromatic418967fa.accept_10_3_5_7_1_330 13 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 237 3 4 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 45 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 237 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 45
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 237 3 3 15 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 237
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 237 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 45 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 237 3 2 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 237 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 45 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 45 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 237 3 1 15 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 45 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 237 (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 45 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  237))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 237 (allA_succ_of_accept 43 44 237 (accept_3_4 43 44
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 237
  (Polychromatic418967fa.accept_9_6_8_3_1_183 42 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 237 (accept_3_4 40 44 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 44 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 38
  44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 237 (accept_3_4 37 44
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 237 (Polychromatic418967fa.accept_7_1_2_6_1_55
  36 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 44 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 44 237 (accept_3_4 34 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  44 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 44 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 44 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 237 (accept_3_4 31 44 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 44 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 44 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 44 237 (accept_3_4 28 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  44 237 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 44 237 (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 44 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 237 (accept_3_4 25 44 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 44 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 44 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 44 237 (accept_3_4 22 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  44 237 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 44 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 44 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 237 (accept_3_4 19 44 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 44 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 44 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 44 237 (accept_3_4 16 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  44 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 44 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 44 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 237 (accept_3_4 13 44 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 44 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 44 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 44 237 (accept_3_4 10 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  44 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 44 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 44 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 237 (accept_3_4 7 44 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 44 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 237 (accept_3_4 4 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  237 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 44 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 44 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 237 (accept_3_4 1 44 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 237)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 237 (allA_succ_of_accept 42 43
  237 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 237 (accept_3_5 41 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 237 (accept_3_5 38 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 43 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 237
  (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 237 (accept_3_5 35 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 237 (accept_3_5 32 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 43 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 237 (accept_3_5 29 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 237 (accept_3_5 26 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 43 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 237 (accept_3_5 23 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 237 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 237 (accept_3_5 20 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 43 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 237 (accept_3_5 17 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 237 (accept_3_5 14 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 43 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 237 (accept_3_5 11 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 237 (accept_3_5 8 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 237 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 43 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 237 (accept_3_5 5 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 43 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 237 (accept_3_5 2 43 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 43 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 237))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 237
  (allA_succ_of_accept 41 42 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 42 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 42 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 237 3 13 14 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 42 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 42 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 237 3 12 14 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  42 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 42 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 42 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 42 237 3 11 14 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 42 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 42 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 237 3 10 14 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 42 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 42 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 42 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 42 237 3 9 14 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 42 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 42 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 237 3 8 14 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 42 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 42 237 3 7 14 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 42 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 42 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 42 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 237 3 6 14 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 42 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 42 237
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 42 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 42 237 3 5 14 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 42 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 42 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 42 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 237 3 4 14 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 42 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 237 3 3 14 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 42 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 42 237 3 2 14 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 42 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 42 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 42 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 237 3 1 14 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 237
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 42 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 42 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 42 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 42 237)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 237
  (allA_succ_of_accept 40 41 237 (accept_3_4 40 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  41 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 41 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 237 (accept_3_4 37 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 41 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 41 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 237 (accept_3_4 34 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 237 (accept_3_4 31 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 237 (Polychromatic418967fa.accept_19_11_3_9_1_8882 30 41 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 237 (accept_3_4 28 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 237 (accept_3_4 25 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 41 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 237
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 237 (accept_3_4 22 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 237 (Polychromatic418967fa.accept_16_5_9_13_1_3845 21 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 237 (accept_3_4 19 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 237 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 41 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 237 (accept_3_4 16 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 237 (accept_3_4 13 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 41 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 237 (accept_3_4 10 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 237 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 237 (accept_3_4 7 41 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 41 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 237
  (Polychromatic418967fa.accept_13_5_2_3_1_1526 5 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 237 (accept_3_4 4 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  237 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 41 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 237 (accept_3_4 1 41 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 237))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 237 (allA_succ_of_accept 39 40 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 237 (accept_3_5 38 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 237 (accept_3_5 35 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 40 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 237 (accept_3_5 32 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 237 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 237 (accept_3_5 29 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 40 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 237
  (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 237 (accept_3_5 26 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 237 (accept_3_5 23 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 40 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 237
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 237 (accept_3_5 20 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 237 (accept_3_5 17 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 40 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 237 (accept_3_5 14 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 237 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 237 (accept_3_5 11 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 40 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 237
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 237 (accept_3_5 8 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 40 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 237 (accept_3_5 5 40 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 40 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 237 (Polychromatic418967fa.accept_16_3_8_13_1_3867
  3 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 237 (accept_3_5 2 40
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 237 (Polychromatic418967fa.accept_6_1_4_3_1_14
  1 40 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  237)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 237 (allA_succ_of_accept 38 39 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 39 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 237 3 12 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 237 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 39 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 237 3 11 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 32 39 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 39 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 237 3 10 13 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 237
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 39 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 39 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 237 3 9 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 39 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 39 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 39 237 3 8 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 39 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 39 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 237 3 7 13 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 237
  (Polychromatic418967fa.accept_15_5_9_12_1_1599 20 39 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 39 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 237 3 6 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 39 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 39 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 39 237 3 5 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 39 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 39 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 39 237 3 4 13 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 39 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 39 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 39 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 237 3 3 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 39 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 39 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 39 237 3 2 13 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 39 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 39 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 237 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 39 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 39 237 3 1 13 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 39 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 39 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 39 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 39 237))))))))))))))))))))))))))))))))))))))) (allB_succ 38 237
  (allA_succ_of_accept 37 38 237 (accept_3_4 37 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  38 237 (Polychromatic418967fa.accept_16_4_6_13_1_1874 36 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 38 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 237 (accept_3_4 34 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 38 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 237 (accept_3_4 31 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 237 (accept_3_4 28 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 237 (accept_3_4 25 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 237 (accept_3_4 22 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 237 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 38 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 237
  (Polychromatic418967fa.accept_15_5_8_12_1_2435 20 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 237 (accept_3_4 19 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 237 (accept_3_4 16 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 237
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 237 (accept_3_4 13 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 237 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 237 (accept_3_4 10 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 38 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 237 (accept_3_4 7 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 38 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 237 (accept_3_4 4 38 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 38
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 237 (accept_3_4 1 38 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 237)))))))))))))))))))))))))))))))))))))) (allB_succ 37 237
  (allA_succ_of_accept 36 37 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 37 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 237 (accept_3_5 35 37 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 33
  37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 237 (accept_3_5 32 37
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 237 (Polychromatic418967fa.accept_7_3_2_6_1_56
  31 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 237
  (Polychromatic418967fa.accept_17_13_3_16_1_5599 30 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 237 (accept_3_5 29 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 37 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 237 (accept_3_5 26 37 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 37 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 237 (accept_3_5 23 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 237 (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 37 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 237 (accept_3_5 20 37 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 237 (Polychromatic418967fa.accept_15_4_7_12_1_5538 19 37
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 237 (accept_3_5 17 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 37 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 237 (accept_3_5 14 37 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 37 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 237
  (Polychromatic418967fa.accept_18_12_1_3_1_7843 12 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 237 (accept_3_5 11 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 237 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 37 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 237 (accept_3_5 8 37 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 37 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 237 (accept_3_5 5 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 37 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 237 (accept_3_5 2 37 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 37 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 237))))))))))))))))))))))))))))))))))))) (allB_succ 36 237
  (allA_succ_of_accept 35 36 237 (Polychromatic418967fa.accept_14_7_8_13_1_3161 35 36 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 36 237 (Polychromatic418967fa.accept_21_13_15_6_1_3556 34 36
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 237 3 11 12 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 237
  (Polychromatic418967fa.accept_13_6_10_3_1_897 32 36 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 36 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 31 36 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 237 3 10 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 237 (Polychromatic418967fa.accept_21_8_15_6_1_8247
  29 36 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 36 237
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 28 36 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 36 237 3 9 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 36 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 36 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 36 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 237 3 8 12 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 36 237 (Polychromatic418967fa.accept_15_7_6_12_1_1614 22 36 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 237 3 7 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 237 (Polychromatic418967fa.accept_11_9_3_6_1_797 20 36 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 36 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 237 3 6 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 36 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 36 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 36 237 3 5 12 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 36 237
  (Polychromatic418967fa.accept_17_14_2_16_1_4380 14 36 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 36 237 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 36 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 237 3 4 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 36 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 36 237
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 36 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 36 237 3 3 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 36 237 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 36 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 237 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 36 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 237 3 2 12 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 36 237 (Polychromatic418967fa.accept_21_4_15_6_1_8327 4 36 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 237 3 1 12 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 36 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 36 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 36 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 36 237)))))))))))))))))))))))))))))))))))) (allB_succ 35 237 (allA_succ_of_accept 34 35 237 (accept_3_4 34
  35 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 237
  (Polychromatic418967fa.accept_9_6_8_3_1_183 33 35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 35 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 237 (accept_3_4 31 35 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 35 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 29
  35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 237 (accept_3_4 28 35
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 237
  (Polychromatic418967fa.accept_12_3_11_9_1_193 27 35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 35 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 237 (accept_3_4 25 35 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 35 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 35 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 23
  35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 237 (accept_3_4 22 35
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 237
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 35 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 237 (accept_3_4 19 35 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 35 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 237 (Polychromatic418967fa.accept_15_2_5_12_1_369
  17 35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 237 (accept_3_4 16
  35 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 237
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 35 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 35 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 237 (accept_3_4 13 35 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 35 237 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 35 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 11
  35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 237 (accept_3_4 10 35
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 237
  (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 35 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 237 (accept_3_4 7 35 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 35 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 5
  35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 237 (accept_3_4 4 35 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 3
  35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 35 237 (accept_3_4 1 35 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35
  237))))))))))))))))))))))))))))))))))) (allB_succ 34 237 (allA_succ_of_accept 33 34 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 237 (accept_3_5 32 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 237 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 34 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 237 (accept_3_5 29 34 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 34 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 237 (accept_3_5 26 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 34 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 237 (accept_3_5 23 34 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 34 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 237
  (Polychromatic418967fa.accept_10_1_4_7_1_374 21 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 237 (accept_3_5 20 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 237 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 34 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 237 (accept_3_5 17 34 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 237 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 34 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 237 (accept_3_5 14 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 34 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 237 (accept_3_5 11 34 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 34 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 237
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 237 (accept_3_5 8 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 34 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 237 (accept_3_5 5 34 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 34 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 237 (accept_3_5 2 34 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 237))))))))))))))))))))))))))))))))))
  (allB_succ 33 237 (allA_succ_of_accept 32 33 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 33 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 237 3 10 11 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 33 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 33 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 237 3 9 11 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 33 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 33 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 237 3 8 11 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 33 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 33 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 237 3 7 11 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 33 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 33 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 237 3 6 11 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 237
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 33 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 33 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 237 3 5 11 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 33 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 237
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 33 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 237 3 4 11 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 33 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 237 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 33 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 237 3 3 11 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 33 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 237 3 2 11 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 237 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 33 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 33 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 237 3 1 11 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 33 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 33 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 237)))))))))))))))))))))))))))))))))
  (allB_succ 32 237 (allA_succ_of_accept 31 32 237 (accept_3_4 31 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 32 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 237 (accept_3_4 28 32 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 237 (Polychromatic418967fa.accept_11_5_10_6_1_793
  27 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 237
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 237 (accept_3_4 25 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 237 (accept_3_4 22 32 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 237 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 32 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 237
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 237 (accept_3_4 19 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 237 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 237 (accept_3_4 16 32 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 32 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 237
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 237 (accept_3_4 13 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 237 (accept_3_4 10 32 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 237
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 237 (accept_3_4 7 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 32 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 237 (accept_3_4 4 32 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  32 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 237 (accept_3_4 1 32 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 237)))))))))))))))))))))))))))))))) (allB_succ 31 237
  (allA_succ_of_accept 30 31 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 237 (accept_3_5 29 31 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  27 31 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 237 (accept_3_5 26
  31 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 31 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 31 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 237 (accept_3_5 23 31 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 237 (Polychromatic418967fa.accept_13_8_5_3_1_427
  21 31 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 237 (accept_3_5 20
  31 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 237
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 31 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 237 (accept_3_5 17 31 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  31 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 237 (accept_3_5 14 31
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 237
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 31 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 237 (Polychromatic418967fa.accept_16_12_15_13_1_3872 12 31 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 237 (accept_3_5 11 31 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 31
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 237 (accept_3_5 8 31 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 7
  31 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 237 (accept_3_5 5 31 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 237 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 31 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 237 (accept_3_5 2 31 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 31 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 237))))))))))))))))))))))))))))))) (allB_succ 30 237
  (allA_succ_of_accept 29 30 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 30 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 30 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 237 3 9 10 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 237
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 30 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 30 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 237 3 8 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 30 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 237 3 7 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 237 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 30 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 237 3 6 10 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 237
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 30 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 30 237 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 30 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 237 3 5 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 237 (Polychromatic418967fa.accept_11_3_8_6_1_788 14 30 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 237
  (Polychromatic418967fa.accept_18_13_12_3_1_3857 13 30 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 237 3 4 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 30 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 237 3 3 10 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 30 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 237 3 2 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 237 (Polychromatic418967fa.accept_20_5_10_17_1_11478 5 30 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 30 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 237 3 1 10 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 30 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 30 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 237)))))))))))))))))))))))))))))) (allB_succ
  29 237 (allA_succ_of_accept 28 29 237 (accept_3_4 28 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 29 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 237 (accept_3_4 25 29 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 24
  29 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 237 (accept_3_4 22 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 237 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 237 (accept_3_4 19 29 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 237 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 29 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 237
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 237 (accept_3_4 16 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 237 (accept_3_4 13 29 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 237
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 11 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 29 237 (accept_3_4 10 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 29 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 29 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 237 (accept_3_4 7 29 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6
  29 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 237 (accept_3_4 4 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  237 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 29 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 237 (accept_3_4 1 29 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 237))))))))))))))))))))))))))))) (allB_succ 28 237 (allA_succ_of_accept 27 28 237
  (Polychromatic418967fa.accept_13_1_2_3_1_911 27 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 237 (accept_3_5 26 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 28 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 237 (accept_3_5 23 28 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 28 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 28 237
  (Polychromatic418967fa.accept_22_21_6_17_1_14155 21 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 28 237 (accept_3_5 20 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 28 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 237 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 28 237 (accept_3_5 17 28 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 28 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 16
  28 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 28 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 28 237 (accept_3_5 14 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  28 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 28 237 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 28 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 28 237 (accept_3_5 11 28 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 28 237 (Polychromatic418967fa.accept_13_10_2_3_1_3025 10 28
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 28 237
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 28 237 (accept_3_5 8 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 28
  237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 28 237 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 28 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 237 (accept_3_5 5 28 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 28 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 28 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 237 (Polychromatic418967fa.accept_15_3_13_12_1_348
  3 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 237 (accept_3_5 2 28
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28 237 (Polychromatic418967fa.accept_6_1_4_3_1_14
  1 28 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 237))))))))))))))))))))))))))))
  (allB_succ 27 237 (allA_succ_of_accept 26 27 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 27 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 27 237 3 8 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 27 237 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 27 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 237 3 7 9 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 237
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 27 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 237 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 27 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 237 3 6 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 27 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 237
  (Polychromatic418967fa.accept_19_16_8_9_1_8858 16 27 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 27 237 3 5 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 27 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 237 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 27 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 237 3 4 9 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 237
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 27 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 237 3 3 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 237 (Polychromatic418967fa.accept_16_8_11_13_1_7265 8 27 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 237
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 27 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 27 237 3 2 9 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 27 237 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 27 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 237 (Polychromatic418967fa.accept_13_4_1_3_1_3058 4 27 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 237 3 1 9 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 237 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 27 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 27 237))))))))))))))))))))))))))) (allB_succ 26 237 (allA_succ_of_accept 25
  26 237 (accept_3_4 25 26 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 26 237
  (Polychromatic418967fa.accept_9_6_8_3_1_183 24 26 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 26 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 237 (accept_3_4 22 26 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 26 237 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 26 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 20
  26 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 26 237 (accept_3_4 19 26
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 26 237
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 26 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 26 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 237 (accept_3_4 16 26 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 26 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 14
  26 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 26 237 (accept_3_4 13 26
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 26 237
  (Polychromatic418967fa.accept_16_12_10_13_1_1042 12 26 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 26 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 237 (accept_3_4 10 26 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 237 (Polychromatic418967fa.accept_18_9_8_3_1_2702 9 26 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 237
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 26 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 237 (accept_3_4 7 26 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 26 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 237 (accept_3_4 4 26 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 237 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  26 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 237 (accept_3_4 1 26 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 237)))))))))))))))))))))))))) (allB_succ 25 237
  (allA_succ_of_accept 24 25 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 25 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 237 (accept_3_5 23 25 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 237
  (Polychromatic418967fa.accept_15_6_10_12_1_2538 21 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 25 237 (accept_3_5 20 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  25 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 25 237 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 25 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 237 (accept_3_5 17 25 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 237 (accept_3_5 14 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 237 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 25 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 237 (accept_3_5 11 25 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 25 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 237 (accept_3_5 8 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  237 (Polychromatic418967fa.accept_15_7_10_12_1_2403 7 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 237 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 25 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 237 (accept_3_5 5 25 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 237 (accept_3_5 2 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  237 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 25 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 237))))))))))))))))))))))))) (allB_succ 24 237 (allA_succ_of_accept 23 24 237
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 24 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 237 3 7 8 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 24 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 24 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 24 237 3 6 8 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 24 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 24 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 24 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 24 237 3 5 8 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 24 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 24 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 24 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 24 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 237 3 4 8 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 24 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 24 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 24 237 3 3 8 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 24 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 24 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 24 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 237 3 2 8 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 24 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 24 237 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 24 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 237 3 1 8 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 24 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 24 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 24 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 237)))))))))))))))))))))))) (allB_succ 23 237 (allA_succ_of_accept 22 23 237 (accept_3_4 22 23 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 237 (Polychromatic418967fa.accept_19_2_4_9_1_1131
  21 23 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 23 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 23 237 (accept_3_4 19 23 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  23 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 23 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 23 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 237 (accept_3_4 16 23 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 23 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 237 (accept_3_4 13 23 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 237 (Polychromatic418967fa.accept_21_12_2_6_1_8230 12 23 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 237 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 237 (accept_3_4 10 23 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 237 (Polychromatic418967fa.accept_16_9_7_13_1_4997 9 23 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 237 (accept_3_4 7 23 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 237 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 23 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 237 (accept_3_4 4 23 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 23 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 237 (accept_3_4 1 23 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 237))))))))))))))))))))))) (allB_succ 22 237
  (allA_succ_of_accept 21 22 237 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 22 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 22 237 (accept_3_5 20 22 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 22 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 22 237 (Polychromatic418967fa.accept_12_6_10_9_1_531
  18 22 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 237 (accept_3_5 17
  22 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 237
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 22 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 22 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 22 237 (accept_3_5 14 22 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 22 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 22 237 (Polychromatic418967fa.accept_7_5_1_6_1_163 12
  22 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 237 (accept_3_5 11 22
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 237
  (Polychromatic418967fa.accept_9_1_4_3_1_201 10 22 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 22 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 22 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 22 237 (accept_3_5 8 22 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 22 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 22 237 (Polychromatic418967fa.accept_9_6_4_3_1_203 6
  22 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 237 (accept_3_5 5 22 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 22 237 (Polychromatic418967fa.accept_10_4_2_7_1_373 4
  22 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 22 237 (accept_3_5 2 22 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22
  237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 237)))))))))))))))))))))) (allB_succ 21 237 (allA_succ_of_accept 20 21 237
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 21 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 237 (Polychromatic418967fa.accept_22_19_21_17_1_6283 19 21 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 237 3 6 7 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 237 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 21 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 237
  (Polychromatic418967fa.accept_10_6_1_7_1_342 16 21 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 21 237 3 5 7 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 21 237 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 21 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 237 (Polychromatic418967fa.accept_22_13_21_17_1_12690 13 21
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 237 3 4 7 79 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 237
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 21 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 237 (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 21 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 237 3 3 7 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 237 (Polychromatic418967fa.accept_14_8_7_13_1_4113 8 21 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 237
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 21 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 21 237 3 2 7 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 21 237 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 21 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 237 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 21 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 237 3 1 7 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 237
  (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 21 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 237 (Polychromatic418967fa.accept_14_1_7_13_1_333 1 21 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 21 237))))))))))))))))))))) (allB_succ 20 237 (allA_succ_of_accept 19 20 237
  (accept_3_4 19 20 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 237
  (Polychromatic418967fa.accept_12_6_8_9_1_553 18 20 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 20 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 20 237 (accept_3_4 16 20 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 20 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 20 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 20 237 (Polychromatic418967fa.accept_9_5_2_3_1_194 14
  20 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 237 (accept_3_4 13 20
  237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 237
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 12 20 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 20 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 20 237 (accept_3_4 10 20 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 20 237 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 20 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 20 237 (Polychromatic418967fa.accept_9_8_2_3_1_447 8
  20 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 237 (accept_3_4 7 20 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 237 (Polychromatic418967fa.accept_9_6_2_3_1_771 6
  20 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 237 (accept_3_4 4 20 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  237 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 20 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 20 237 (Polychromatic418967fa.accept_15_2_5_12_1_369 2 20 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 237 (accept_3_4 1 20 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 237)))))))))))))))))))) (allB_succ 19 237 (allA_succ_of_accept 18 19 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 237 (accept_3_5 17 19 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 19 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 237 (accept_3_5 14 19 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 237 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 19 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 237
  (Polychromatic418967fa.accept_10_2_9_7_1_720 12 19 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 237 (accept_3_5 11 19 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 237 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 19 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 237 (accept_3_5 8 19 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 237 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 19 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 237 (accept_3_5 5 19 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 237 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 19 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 237 (accept_3_5 2 19 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 19 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 237))))))))))))))))))) (allB_succ 18 237 (allA_succ_of_accept 17
  18 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 18 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 18 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 237 3 5 6 79 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 237 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  18 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 237
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 18 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 237 3 4 6 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 18 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 237 3 3 6 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 237
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 18 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 237 3 2 6 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 18 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 237
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 18 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 237 3 1 6 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 237 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 18 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 237 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 18 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 237)))))))))))))))))) (allB_succ 17 237
  (allA_succ_of_accept 16 17 237 (accept_3_4 16 17 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 17 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 237 (accept_3_4 13 17 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 237 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 17 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 237
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 17 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 237 (accept_3_4 10 17 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 17 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 17 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 237 (accept_3_4 7 17 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 17 237 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 17 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 237 (Polychromatic418967fa.accept_9_5_8_3_1_437 5
  17 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 237 (accept_3_4 4 17 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17 237 (Polychromatic418967fa.accept_12_3_5_9_1_176 3
  17 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 237
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 17 237 (accept_3_4 1 17 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17
  237))))))))))))))))) (allB_succ 16 237 (allA_succ_of_accept 15 16 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 16
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 237 (accept_3_5 14 16 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  16 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 237
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 16 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 237 (accept_3_5 11 16 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 16 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 237 (Polychromatic418967fa.accept_21_9_16_6_1_5134 9 16 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 237 (accept_3_5 8 16 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 237
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 16 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 237 (accept_3_5 5 16 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  237 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 16 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 237 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 16 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 237 (accept_3_5 2 16 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 16 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 237)))))))))))))))) (allB_succ 15 237 (allA_succ_of_accept 14 15
  237 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 15 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 237 3 4 5 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 15 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 15 237 3 3 5 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 15 237 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 15 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 237 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 15 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 15 237 3 2 5 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 15 237
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 15 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 15 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 15 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 237 3 1 5 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 15 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 15 237))))))))))))))) (allB_succ 14 237 (allA_succ_of_accept 13 14 237 (accept_3_4 13 14 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 237 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 14 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 14 237
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 14 237 (accept_3_4 10 14 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  14 237 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 14 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 14 237 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 14 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 14 237 (accept_3_4 7 14 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 14 237 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 14 237 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 14 237
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 14 237 (accept_3_4 4 14 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 14
  237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 14 237 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 14 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 237 (accept_3_4 1 14 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 14 237)))))))))))))) (allB_succ 13 237 (allA_succ_of_accept 12 13 237
  (Polychromatic418967fa.accept_17_12_13_16_1_3226 12 13 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 237 (accept_3_5 11 13 237 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 237 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 13 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 237 (Polychromatic418967fa.accept_17_9_13_16_1_3266 9 13 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 237 (accept_3_5 8 13 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 237 (Polychromatic418967fa.accept_9_7_4_3_1_204 7
  13 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 237
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 13 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 237 (accept_3_5 5 13 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  237 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 237 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 13 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 237 (accept_3_5 2 13 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 237 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 13 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 237))))))))))))) (allB_succ 12 237 (allA_succ_of_accept 11 12
  237 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 12 237 (Polychromatic418967fa.accept_16_10_12_13_1_4950 10 12 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 237 3 3 4 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 12 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 12 237
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 12 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 12 237 3 2 4 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 12 237 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 12 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 237 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 12 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 12 237 3 1 4 79 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 12 237
  (Polychromatic418967fa.accept_13_2_12_3_1_415 2 12 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 12 237 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 12 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 237)))))))))))) (allB_succ 11 237 (allA_succ_of_accept 10 11 237
  (accept_3_4 10 11 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 237
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 11 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 237 (accept_3_4 7 11 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 237 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  11 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 237 (accept_3_4 4 11 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 237 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  11 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 237 (accept_3_4 1 11 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  237))))))))))) (allB_succ 10 237 (allA_succ_of_accept 9 10 237 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 10 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 237 (accept_3_5 8 10 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 237
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 10 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 10 237 (accept_3_5 5 10 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 10
  237 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 10 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 10 237 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 237 (accept_3_5 2 10 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 10 237 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 237)))))))))) (allB_succ 9 237 (allA_succ_of_accept 8 9 237
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 237 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 9 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 237 3 2 3 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 237 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 9 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 237
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 9 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 237 3 1 3 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 237 (Polychromatic418967fa.accept_10_2_9_7_1_720 2 9 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 237 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 9 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 237))))))))) (allB_succ 8 237
  (allA_succ_of_accept 7 8 237 (accept_3_4 7 8 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 237
  (Polychromatic418967fa.accept_9_6_8_3_1_183 6 8 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 8 237 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 8 237 (accept_3_4 4 8 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 8 237 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 8 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 8 237 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 8
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 237 (accept_3_4 1 8 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 237)))))))) (allB_succ 7 237 (allA_succ_of_accept 6 7 237
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 237 (accept_3_5 5 7 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 237
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 237 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 7 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 237 (accept_3_5 2 7 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 237 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 7 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 237))))))) (allB_succ 6 237 (allA_succ_of_accept 5 6 237
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 6 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 237 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 6 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 237 3 1 2 79 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 237 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 6 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 237
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 6 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 237)))))) (allB_succ 5 237 (allA_succ_of_accept 4 5 237 (accept_3_4 4 5 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 237 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 5 237 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 237 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 237 (accept_3_4 1 5 237
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 237))))) (allB_succ 4 237 (allA_succ_of_accept 3 4 237
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 4 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 237 (accept_3_5 2 4 237 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 237
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 237)))) (allB_succ 3 237 (allA_succ_of_accept 2 3 237 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 237
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 237
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 3 237 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 237))) (allB_succ 2 237 (allA_succ_of_accept 1 2 237 (accept_3_4 1 2 237 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 237)) (allB_two
  237))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


