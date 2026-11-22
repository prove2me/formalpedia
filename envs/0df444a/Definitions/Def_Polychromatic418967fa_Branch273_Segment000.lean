-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch273_Segment000
-- name    : Polychromatic418967fa_Branch273_Segment000
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:48:53.540245+00:00
-- url     : https://prove2.me/theorems/ba356f56-111a-4939-b26b-07215b453be0
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

def Polychromatic418967fa.branch_273_segment_000 : allB 100 273 :=
  allB_succ 99 273 (allA_succ_of_accept 98 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 99 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 99 273
  (Polychromatic418967fa.accept_12_1_3_9_1_174 97 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 99 273 3 32 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 99 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 95 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 93 99 273 3 31 33 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 99 273
  (Polychromatic418967fa.accept_14_8_1_7_1_3725 92 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 99 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 91 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 99 273 3 30 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 99 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 89
  99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 99 273
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 88 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 99 273 3 29 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 86 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 99 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 85 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 99 273 3 28 33 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 99 273
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 83 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 99 273 3 27 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 99 273 (Polychromatic418967fa.accept_15_5_9_3_1_528 80
  99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 99 273
  (Polychromatic418967fa.accept_12_7_3_9_1_999 79 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 99 273 3 26 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 99 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 77 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 273 (Polychromatic418967fa.accept_10_6_9_3_1_935 76 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 99 273 3 25 33 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 99 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 99 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 73 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 99 273 3 24 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 99 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  71 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 99 273 3 23 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 99 273 (Polychromatic418967fa.accept_15_8_9_3_1_1194 68 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 99 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 67 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 99 273 3 22 33 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 99 273
  (Polychromatic418967fa.accept_12_5_3_9_1_541 65 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 99 273 (Polychromatic418967fa.accept_10_4_9_3_1_1907 64 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 99 273 3 21 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 99
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 99 273
  (Polychromatic418967fa.accept_12_1_3_9_1_174 61 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 99 273 3 20 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 99 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 59 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 99 273 3 19 33 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 99 273
  (Polychromatic418967fa.accept_10_6_9_3_1_935 56 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 99 273 3 18 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 99 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 53
  99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 273
  (Polychromatic418967fa.accept_16_4_3_1_1_8843 52 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 99 273 3 17 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 99 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 49 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 99 273 3 16 33 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 99 273
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 99 273 3 15 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 273 (Polychromatic418967fa.accept_10_4_9_3_1_1907
  44 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 273
  (Polychromatic418967fa.accept_12_7_3_9_1_999 43 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 273 3 14 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 273 (Polychromatic418967fa.accept_15_10_9_3_1_1947 40 99
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 273 3 13 33 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 273 3 12 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 273 3 11 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 273 (Polychromatic418967fa.accept_18_14_9_3_1_6421 32 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 273 3 10 33 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 273
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 273 (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 273 3 9 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 273
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 273 3 8 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 273 3 7 33 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 273
  (Polychromatic418967fa.accept_14_6_1_7_1_2775 20 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 273 3 6 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 273
  (Polychromatic418967fa.accept_10_6_9_3_1_935 16 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 273 3 5 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 273 3 4 33 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 273
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 273 3 3 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 273 (Polychromatic418967fa.accept_14_8_1_7_1_3725 8 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 273
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 273 3 2 33 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 273 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 99 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 273 3 1 33 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 99 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 99 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 98
  273 (allA_succ_of_accept 97 98 273 (accept_3_4 97 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 98 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 96 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 98 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 98 273 (accept_3_4 94 98 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 98 273 (Polychromatic418967fa.accept_22_5_10_9_1_15147 93 98 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 98 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 92 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 91 98 273 7 13 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 90 98 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 90 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 98 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 98 273 (accept_3_4 88 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 87
  98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 98 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 86 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 98 273 (accept_3_4 85 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 98
  273 7 12 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83
  98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 98 273 (accept_3_4 82 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 98 273 (Polychromatic418967fa.accept_10_1_8_3_1_947 81 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 98 273 (Polychromatic418967fa.accept_15_5_8_3_1_556 80 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 98 273 (accept_3_4 79 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 98 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 78
  98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 98 273 7 11 14 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 98 273 (accept_3_4 76
  98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 98 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 98 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 74 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 98 273 (accept_3_4 73 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 98 273 (Polychromatic418967fa.accept_15_12_8_3_1_1995 72 98 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 98 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 71 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 98 273 7 10 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 98 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 98 273 (Polychromatic418967fa.accept_9_5_8_3_1_437 68 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 98 273 (accept_3_4 67 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 98 273 (Polychromatic418967fa.accept_10_6_8_3_1_930
  66 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 98 273
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 98 273 (accept_3_4 64 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 98
  273 7 9 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  98 273 (Polychromatic418967fa.accept_19_5_3_7_1_10042 62 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 98 273 (accept_3_4 61 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 98 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 98 273 (accept_3_4 58 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 98 273 (Polychromatic418967fa.accept_15_12_8_3_1_1995
  57 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 273 7 8 14 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 273 (accept_3_4 55
  98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 98 273
  (Polychromatic418967fa.accept_12_6_2_9_1_537 54 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 98 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 98 273 (accept_3_4 52 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 98 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 98 273 (Polychromatic418967fa.accept_9_5_8_3_1_437 50
  98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 98 273 7 7 14 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 98 273
  (Polychromatic418967fa.accept_17_14_13_1_1_3356 48 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 98 273 (accept_3_4 46 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 98 273 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 98 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 98 273 (Polychromatic418967fa.accept_16_12_2_1_1_1215
  44 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 98 273 (accept_3_4 43
  98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 273 7 6 14 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 273
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 98 273 (accept_3_4 40 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 98 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 98 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 98 273 (accept_3_4 37 98 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 98 273 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 98 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 98 273 7 5 14 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 98 273 (accept_3_4 34 98 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 98 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 98 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 98 273 (accept_3_4 31 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  98 273 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 98 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 98 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 273 7 4 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 98 273
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 98 273 (accept_3_4 25 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  98 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 98 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 98 273 (accept_3_4 22 98 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 98 273 7 3 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 98 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 98 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 98 273 (accept_3_4 19 98 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 98 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 98 273
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 98 273 (accept_3_4 16 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 98 273 7 2 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 98 273 (accept_3_4 13 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 98 273 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 98 273 (accept_3_4 10 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 98 273 (Polychromatic418967fa.accept_15_9_8_3_1_557 9
  98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 98 273
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 98 273 7 1 14 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 98 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 98 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 98 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 98 273 (accept_3_4 4 98 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 98 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 98
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 98 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 98 273 (accept_3_4 1 98 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 97
  273 (allA_succ_of_accept 96 97 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 96 97 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 97 273 (accept_3_5 95 97 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 94 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 97 273
  (Polychromatic418967fa.accept_19_17_2_7_1_11422 93 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 97 273 (accept_3_5 92 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91
  97 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 91 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 97 273 (Polychromatic418967fa.accept_14_6_13_7_1_2015 90 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 97 273 (accept_3_5 89 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 97 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 97 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 87 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 97 273 (accept_3_5 86 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  97 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 85 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 97 273 (Polychromatic418967fa.accept_10_4_7_3_1_54 84 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 97 273 (accept_3_5 83 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 97 273
  (Polychromatic418967fa.accept_17_13_12_1_1_4524 81 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 97 273 (accept_3_5 80 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  97 273 (Polychromatic418967fa.accept_15_4_7_3_1_119 79 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 97 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 78 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 97 273 (accept_3_5 77 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 97 273
  (Polychromatic418967fa.accept_10_5_7_3_1_561 75 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 97 273 (accept_3_5 74 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  97 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 97 273 (Polychromatic418967fa.accept_15_12_7_3_1_1940 72 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 97 273 (accept_3_5 71 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 97 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 97 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 69 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 97 273 (accept_3_5 68 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  97 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 97 273 (Polychromatic418967fa.accept_10_6_7_3_1_547 66 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 97 273 (accept_3_5 65 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 97 273
  (Polychromatic418967fa.accept_12_3_1_9_1_202 63 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 97 273 (accept_3_5 62 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  97 273 (Polychromatic418967fa.accept_19_4_2_7_1_4458 61 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 97 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 97 273 (accept_3_5 59 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 97 273
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 57 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 97 273 (accept_3_5 56 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  97 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 97 273 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 97 273 (accept_3_5 53 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 97 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 273 (accept_3_5 50 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 273 (Polychromatic418967fa.accept_14_6_13_7_1_2015 48 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 273 (accept_3_5 47 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 97 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 273
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 273 (accept_3_5 44 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 273 (Polychromatic418967fa.accept_14_1_13_7_1_1205 43 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 273 (accept_3_5 41 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 273
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 273 (accept_3_5 38 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 273 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 273 (accept_3_5 35 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 273 (accept_3_5 32 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 273 (Polychromatic418967fa.accept_17_13_12_1_1_4524 30 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 273 (accept_3_5 29 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 97 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 273
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 273 (accept_3_5 26 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 273 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 273 (accept_3_5 23 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 273
  (Polychromatic418967fa.accept_26_21_19_13_1_16746 21 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 97 273 (accept_3_5 20 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 97 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 97 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 273 (Polychromatic418967fa.accept_26_18_19_13_1_789 18 97
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 273 (accept_3_5 17 97 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 273 (accept_3_5 14 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 273 (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 273 (accept_3_5 11 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 97 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 273
  (Polychromatic418967fa.accept_18_9_7_3_1_3871 9 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 273 (accept_3_5 8 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  273 (Polychromatic418967fa.accept_25_7_22_23_1_16745 7 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 97 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 273 (accept_3_5 5 97 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 97 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 97 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 273
  (Polychromatic418967fa.accept_12_3_1_9_1_202 3 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 97 273 (accept_3_5 2 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97
  273 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 97 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 97 273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 96 273 (allA_succ_of_accept 95 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 95 96 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 94 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 93 96 273 3 31 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 92 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 92 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 91 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 96 273 3 30 32 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 96 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 89 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 96 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 88 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 96 273 3 29 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 86
  96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 85 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 96 273 3 28 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 83 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 82 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 96 273 3 27 32 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 96 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 80 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 96 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 79 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 96 273 3 26 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 77
  96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 76 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 96 273 3 25 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 74 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 273 3 24 32 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 71 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 96 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 70 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 96 273 3 23 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 68
  96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 96 273 3 22 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 65 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 96 273 3 21 32 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 96 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 62 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 96 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 273 3 20 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 59
  96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 96 273 3 19 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 273 3 18 32 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 96 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 96 273 3 17 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 50
  96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 96 273 3 16 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 96 273 3 15 32 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 96 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 96 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 273 3 14 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 96 273 3 13 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 273 3 12 32 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 96 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 96 273 3 11 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 96 273 3 10 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 96 273 3 9 32 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 96 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 96 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 273 3 8 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 96 273 3 7 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 273 3 6 32 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 96 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 96 273 3 5 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 273 3 4 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 96 273 3 3 32 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 96 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 96 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 273 3 2 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 96 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 96 273 3 1 32 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 96 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 96 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 96 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 96 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 95 273
  (allA_succ_of_accept 94 95 273 (accept_3_4 94 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93
  95 273 (Polychromatic418967fa.accept_11_5_7_9_1_2696 93 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 95 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 92 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 95 273 (accept_3_4 91 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 95 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 89 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 95 273 (accept_3_4 88 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  95 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 87 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 95 273 (accept_3_4 85 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 95 273 (Polychromatic418967fa.accept_15_9_5_3_1_554 84 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 95 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 83 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 95 273 (accept_3_4 82 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  95 273 (Polychromatic418967fa.accept_15_6_5_3_1_1988 81 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 95 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 95 273 (accept_3_4 79 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 95 273
  (Polychromatic418967fa.accept_10_7_5_3_1_542 77 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 95 273 (accept_3_4 76 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  95 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 75 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 95 273 (accept_3_4 73 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 95 273 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 95 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 71 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 95 273 (accept_3_4 70 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  95 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 95 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 95 273 (accept_3_4 67 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 95 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 65 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 95 273 (accept_3_4 64 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  95 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 95 273 (accept_3_4 61 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 95 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 95 273
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 59 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 95 273 (accept_3_4 58 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  95 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 95 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 95 273 (accept_3_4 55 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 95 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 95 273 (accept_3_4 52 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  95 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 95 273 (accept_3_4 49 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 273 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 95 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 95 273 (accept_3_4 46 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  95 273 (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 95 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 95 273 (accept_3_4 43 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 273
  (Polychromatic418967fa.accept_17_7_10_1_1_4488 41 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 95 273 (accept_3_4 40 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  95 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 273 (accept_3_4 37 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 95 273 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 95 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 95 273 (accept_3_4 34 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  95 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 95 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 273 (accept_3_4 31 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 273 (accept_3_4 28 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 273 (accept_3_4 25 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 273
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 273 (accept_3_4 22 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 273 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 273 (accept_3_4 19 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 273 (accept_3_4 16 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 273 (accept_3_4 13 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 273 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 273 (accept_3_4 10 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 273 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 273 (accept_3_4 7 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 95 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 273
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 273 (accept_3_4 4 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  273 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 95 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 95 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 273 (accept_3_4 1 95 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 95
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 94 273
  (allA_succ_of_accept 93 94 273 (Polychromatic418967fa.accept_16_13_14_1_1_2094 93 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 94 273 (accept_3_5 92 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 94 273 (Polychromatic418967fa.accept_12_6_10_9_1_531
  90 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 94 273 (accept_3_5 89
  94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 94 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 88 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 94 273 (accept_3_5 86 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 94 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 94 273 (Polychromatic418967fa.accept_16_4_14_1_1_1241
  84 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 94 273 (accept_3_5 83
  94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 94 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 82 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 94 273 (Polychromatic418967fa.accept_14_11_10_7_1_1948 81 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 94 273 (accept_3_5 80 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 94 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 78
  94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 94 273 (accept_3_5 77 94
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 94 273
  (Polychromatic418967fa.accept_15_1_4_3_1_1928 76 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 94 273 (accept_3_5 74 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 94 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 94 273
  (Polychromatic418967fa.accept_19_15_18_7_1_10018 72 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 94 273 (accept_3_5 71 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 94 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 94 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 94 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 94 273 (accept_3_5 68 94 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 67
  94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 94 273
  (Polychromatic418967fa.accept_12_6_10_9_1_531 66 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 94 273 (accept_3_5 65 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  94 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 94 273 (accept_3_5 62 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 94 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 94 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 94 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 94 273 (accept_3_5 59 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  94 273 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 94 273 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 94 273 (accept_3_5 56 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 94 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 94 273
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 94 273 (accept_3_5 53 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  94 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 273 (accept_3_5 50 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 94 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 273
  (Polychromatic418967fa.accept_19_10_18_7_1_12729 48 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 94 273 (accept_3_5 47 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 94 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 94 273 (Polychromatic418967fa.accept_14_3_10_7_1_3773 45 94
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 273 (accept_3_5 44 94 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 273 (accept_3_5 41 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 273 (Polychromatic418967fa.accept_23_17_2_20_1_13543 40 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 273 (accept_3_5 38 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 94 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 273
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 273 (accept_3_5 35 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 273 (accept_3_5 32 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 273
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 273 (accept_3_5 29 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 273 (accept_3_5 26 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 94 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 273 (accept_3_5 23 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 273 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 273 (Polychromatic418967fa.accept_20_1_14_13_1_6735 21 94 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 273 (accept_3_5 20 94 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 273
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 273 (accept_3_5 17 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 273 (accept_3_5 14 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 94 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 273
  (Polychromatic418967fa.accept_19_12_18_7_1_16744 12 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 94 273 (accept_3_5 11 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 94 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 94 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 94 273 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 94 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 273 (accept_3_5 8 94 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 273 (accept_3_5 5 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  273 (Polychromatic418967fa.accept_14_4_10_7_1_1946 4 94 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 94 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 273 (accept_3_5 2 94 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 94 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 94 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 93 273
  (allA_succ_of_accept 92 93 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 92 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 93 273 (Polychromatic418967fa.accept_19_15_17_7_1_8734 91 93
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 93 273 3 30 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 93 273
  (Polychromatic418967fa.accept_14_5_9_7_1_590 89 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 93 273 (Polychromatic418967fa.accept_23_19_1_20_1_13532 88 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 93 273 3 29 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 93 273 (Polychromatic418967fa.accept_14_2_9_7_1_5633
  86 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 93 273
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 85 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 93 273 3 28 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 93 273 (Polychromatic418967fa.accept_16_3_13_1_1_1206 83 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 93 273 (Polychromatic418967fa.accept_14_12_9_7_1_2762 82 93
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 93 273 3 27 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 93 273
  (Polychromatic418967fa.accept_22_14_5_9_1_15124 80 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 93 273 (Polychromatic418967fa.accept_17_11_8_1_1_3362 79 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 93 273 3 26 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 93 273 (Polychromatic418967fa.accept_17_9_8_1_1_7036
  77 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 93 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 76 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 93 273 3 25 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 93 273 (Polychromatic418967fa.accept_23_5_1_20_1_16743 74 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 273 (Polychromatic418967fa.accept_11_7_5_9_1_884 73 93 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 93 273 3 24 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 93 273
  (Polychromatic418967fa.accept_26_19_15_13_1_13133 71 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 93 273 (Polychromatic418967fa.accept_19_13_17_7_1_12726 70 93 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 93 273 3 23 31 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 93 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 68 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 93 273 (Polychromatic418967fa.accept_16_3_13_1_1_1206 67 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 93 273 3 22 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 93 273
  (Polychromatic418967fa.accept_23_19_1_20_1_13532 65 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 93 273 (Polychromatic418967fa.accept_27_10_12_3_1_16742 64 93 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 93 273 3 21 31 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 93 273
  (Polychromatic418967fa.accept_11_7_5_9_1_884 62 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 93 273 (Polychromatic418967fa.accept_14_5_9_7_1_590 61 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 93 273 3 20 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 93 273 (Polychromatic418967fa.accept_19_2_17_7_1_8735
  59 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 273
  (Polychromatic418967fa.accept_14_2_9_7_1_5633 58 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 93 273 3 19 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 93 273 (Polychromatic418967fa.accept_19_18_17_7_1_8699 56 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 273 (Polychromatic418967fa.accept_17_4_8_1_1_5740 55 93 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 93 273 3 18 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 93 273
  (Polychromatic418967fa.accept_16_5_13_1_1_2084 53 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 93 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 93 273 3 17 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 93 273 (Polychromatic418967fa.accept_23_4_1_20_1_16741
  50 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 273
  (Polychromatic418967fa.accept_23_3_1_20_1_15080 49 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 93 273 3 16 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 93 273 (Polychromatic418967fa.accept_14_5_9_7_1_590 47 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 273 (Polychromatic418967fa.accept_16_14_13_1_1_5278 46 93
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 273 3 15 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 273 (Polychromatic418967fa.accept_17_9_8_1_1_7036 43 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 93 273 3 14 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 93 273 (Polychromatic418967fa.accept_16_9_13_1_1_3069
  41 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 273
  (Polychromatic418967fa.accept_11_7_5_9_1_884 40 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 93 273 3 13 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 93 273 (Polychromatic418967fa.accept_17_4_8_1_1_5740 38 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 273 (Polychromatic418967fa.accept_16_5_13_1_1_2084 37 93
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 273 3 12 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 273
  (Polychromatic418967fa.accept_16_3_13_1_1_1206 35 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 273 (Polychromatic418967fa.accept_19_15_17_7_1_8734 34 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 93 273 3 11 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 93 273
  (Polychromatic418967fa.accept_19_13_17_7_1_12726 32 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 93 273 (Polychromatic418967fa.accept_25_6_18_23_1_5963 31 93 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 273 3 10 31 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 273
  (Polychromatic418967fa.accept_11_7_5_9_1_884 29 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 273 3 9 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 273 (Polychromatic418967fa.accept_14_12_9_7_1_2762 26 93 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 273
  (Polychromatic418967fa.accept_16_9_13_1_1_3069 25 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 93 273 3 8 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 93 273 (Polychromatic418967fa.accept_22_1_5_9_1_4114 23 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 273 (Polychromatic418967fa.accept_24_22_21_9_1_16740 22 93
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 273 3 7 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 20 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 273 (Polychromatic418967fa.accept_14_5_9_7_1_590 19 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 273 3 6 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 273 (Polychromatic418967fa.accept_25_17_18_23_1_11555 17 93
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 273
  (Polychromatic418967fa.accept_14_2_9_7_1_5633 16 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 93 273 3 5 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 93 273 (Polychromatic418967fa.accept_16_14_13_1_1_5278 14 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 273 (Polychromatic418967fa.accept_19_13_17_7_1_12726 13 93
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 273 3 4 31 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 273
  (Polychromatic418967fa.accept_17_11_8_1_1_3362 11 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 273 (Polychromatic418967fa.accept_19_10_17_7_1_12725 10 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 273 3 3 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 273 (Polychromatic418967fa.accept_26_8_15_13_1_16739 8 93 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 273
  (Polychromatic418967fa.accept_11_7_5_9_1_884 7 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 93 273 3 2 31 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 93 273 (Polychromatic418967fa.accept_14_5_9_7_1_590 5 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 93 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 273 3 1 31 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 273
  (Polychromatic418967fa.accept_14_2_9_7_1_5633 2 93 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 273 (Polychromatic418967fa.accept_22_1_5_9_1_4114 1 93 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 92 273
  (allA_succ_of_accept 91 92 273 (accept_3_4 91 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90
  92 273 (Polychromatic418967fa.accept_11_2_4_9_1_484 90 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 89 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 92 273 (accept_3_4 88 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 92 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 87 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 92 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 86 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 92 273 (accept_3_4 85 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  92 273 (Polychromatic418967fa.accept_16_4_12_1_1_1204 84 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 83 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 92 273 (accept_3_4 82 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 92 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 81 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 92 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 80 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 92 273 (accept_3_4 79 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  92 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 92 273 (accept_3_4 76 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 92 273 (Polychromatic418967fa.accept_10_5_2_3_1_239 75 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 92 273
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 74 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 92 273 (accept_3_4 73 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  92 273 (Polychromatic418967fa.accept_15_12_2_3_1_1146 72 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 92 273 (accept_3_4 70 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 92 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 92 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 68 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 92 273 (accept_3_4 67 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  92 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 92 273 (accept_3_4 64 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 92 273 (Polychromatic418967fa.accept_18_9_2_3_1_5082 63 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 92 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 62 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 92 273 (accept_3_4 61 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  92 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 92 273 (accept_3_4 58 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 92 273 (Polychromatic418967fa.accept_11_2_4_9_1_484 57 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 92 273
  (Polychromatic418967fa.accept_16_8_12_1_1_7720 56 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 92 273 (accept_3_4 55 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  92 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 92 273 (accept_3_4 52 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 92 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 92 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 92 273 (accept_3_4 49 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  92 273 (Polychromatic418967fa.accept_14_6_8_7_1_589 48 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 92 273 (accept_3_4 46 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 92 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 92 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 92 273 (accept_3_4 43 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  92 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 92 273 (accept_3_4 40 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 92 273 (Polychromatic418967fa.accept_20_19_12_13_1_2602 39 92 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 92 273
  (Polychromatic418967fa.accept_22_16_4_9_1_5663 38 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 92 273 (accept_3_4 37 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  92 273 (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 92 273 (accept_3_4 34 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 92 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 92 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 92 273 (accept_3_4 31 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  92 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 92 273 (accept_3_4 28 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 92 273 (Polychromatic418967fa.accept_14_13_8_7_1_1224 27 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 92 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 92 273 (accept_3_4 25 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  92 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 92 273 (accept_3_4 22 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 92 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 92 273
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 92 273 (accept_3_4 19 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  92 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 92 273 (accept_3_4 16 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 92 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 92 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 92 273 (accept_3_4 13 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  92 273 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 92 273 (accept_3_4 10 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 92 273 (Polychromatic418967fa.accept_18_9_2_3_1_5082 9 92 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 92 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 92 273 (accept_3_4 7 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 92
  273 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 92 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 92 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 92 273 (accept_3_4 4 92 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 92 273 (Polychromatic418967fa.accept_20_3_12_13_1_3836 3 92 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 92 273 (Polychromatic418967fa.accept_11_2_4_9_1_484 2
  92 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 92 273 (accept_3_4 1 92 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 91 273
  (allA_succ_of_accept 90 91 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 91 273 (accept_3_5 89 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 91 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 88 91 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 91 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 87
  91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 273 (accept_3_5 86 91
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 273
  (Polychromatic418967fa.accept_9_4_1_3_1_190 85 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 91 273 7 12 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 91 273 (accept_3_5 83 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 273 (Polychromatic418967fa.accept_15_6_1_3_1_2852 81 91 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 273 (accept_3_5 80 91 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 79 91 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 91 273 13 6 7 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 91 273 7 11 13 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 91 273
  (Polychromatic418967fa.accept_6_4_1_3_1_77 76 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 91 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 75 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 273 (accept_3_5 74 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 91 273 (Polychromatic418967fa.accept_15_13_1_3_1_1972 73 91 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 273
  (Polychromatic418967fa.accept_10_2_1_3_1_233 72 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 273 (accept_3_5 71 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 91
  273 7 10 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  91 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 91 273 (accept_3_5 68 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 91 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 91 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 91 273 13 5 7 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 91 273
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 91 273 7 9 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 91 273 (accept_3_5 62 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  91 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 91 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 60 91 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 91 273 (accept_3_5 59 91 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 91 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 91 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 91 273
  (Polychromatic418967fa.accept_23_11_22_20_1_16738 57 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 91 273 7 8 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 91 273 (Polychromatic418967fa.accept_19_17_15_7_1_10030 55 91 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 273 (accept_3_5 53 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 91
  273 13 4 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  91 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 91 273 (accept_3_5 50 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 91 273 7 7 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 91 273 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 273 (accept_3_5 47 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 91 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 273 (Polychromatic418967fa.accept_18_9_1_3_1_6451
  45 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 273 (accept_3_5 44
  91 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 273
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 91 273 7 6 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 91 273 (accept_3_5 41 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 91 273 13 3 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 91 273 (accept_3_5 38 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 91 273 (Polychromatic418967fa.accept_17_3_6_1_1_8382 37 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 273 (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 91 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 91 273 7 5 13 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 91 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 91 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 273 (accept_3_5 32 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 91 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 91 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 273 (accept_3_5 29 91
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 91 273 7 4 13 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 91 273
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 91 273 13 2 7 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 91 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 91 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 273 (accept_3_5 23 91 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 91 273 7 3 13 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 91 273 (accept_3_5 20
  91 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 273
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 91 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 273 (accept_3_5 17 91 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 91 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 91 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 15
  91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 91 273 7 2 13 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 91 273 13 1 7 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 91 273
  (Polychromatic418967fa.accept_10_2_1_3_1_233 12 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 273 (accept_3_5 11 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 273 (Polychromatic418967fa.accept_18_9_1_3_1_6451 9 91 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 273 (accept_3_5 8 91 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 91 273 7 1 13 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 91 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 273 (accept_3_5 5 91 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 91 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 273
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 91 273 (accept_3_5 2 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91
  273 (Polychromatic418967fa.accept_22_1_3_9_1_9082 1 91 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 91
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 90 273
  (allA_succ_of_accept 89 90 273 (Polychromatic418967fa.accept_16_9_10_1_1_2998 89 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 90 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 88 90 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 90 273 3 29 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 90 273
  (Polychromatic418967fa.accept_12_2_6_9_1_19 86 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 90 273 (Polychromatic418967fa.accept_14_1_6_7_1_1936 85 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 90 273 3 28 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 90 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 83
  90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 90 273
  (Polychromatic418967fa.accept_12_10_6_9_1_549 82 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 90 273 3 27 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 80 90 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608 80 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 90 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 90 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 273 3 26 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 273
  (Polychromatic418967fa.accept_20_17_10_13_1_1400 77 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 90 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 76 90 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 90 273 3 25 30 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 90 273
  (Polychromatic418967fa.accept_12_2_6_9_1_19 74 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 90 273 (Polychromatic418967fa.accept_11_7_2_9_1_480 73 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 273 3 24 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 90 273
  (Polychromatic418967fa.accept_11_4_2_9_1_496 70 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 90 273 3 23 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 90 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608 68 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 90 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 90 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 273 3 22 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 273
  (Polychromatic418967fa.accept_19_8_14_7_1_10047 65 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 90 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 64 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 90 273 3 21 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 90 273 (Polychromatic418967fa.accept_11_7_2_9_1_480 62
  90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 90 273
  (Polychromatic418967fa.accept_19_4_14_7_1_5863 61 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 90 273 3 20 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 90 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 90 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 90 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 90 273 3 19 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 90 273
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 90 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 273 3 18 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 273 (Polychromatic418967fa.accept_19_15_14_7_1_2044
  53 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 90 273
  (Polychromatic418967fa.accept_12_4_6_9_1_548 52 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 90 273 3 17 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 90 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 90 273 (Polychromatic418967fa.accept_19_11_14_7_1_4473 49 90
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 273 3 16 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 90 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 90 273 3 15 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 90 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  44 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 273 3 14 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 273 (Polychromatic418967fa.accept_14_13_6_7_1_2013 41 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 90 273 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 90 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 90 273 3 13 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 90 273
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 90 273 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 273 3 12 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 90 273
  (Polychromatic418967fa.accept_12_10_6_9_1_549 34 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 90 273 3 11 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 90 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 90 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 273 3 10 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 273
  (Polychromatic418967fa.accept_11_7_2_9_1_480 29 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 90 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 90 273 3 9 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 90 273 (Polychromatic418967fa.accept_11_4_2_9_1_496 26 90 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 90 273
  (Polychromatic418967fa.accept_16_9_10_1_1_2998 25 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 90 273 3 8 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 90 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 90 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 90 273 3 7 30 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 90 273
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 90 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 273 3 6 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 273 (Polychromatic418967fa.accept_20_17_10_13_1_1400 17 90
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 273
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 90 273 3 5 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 90 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 273 (Polychromatic418967fa.accept_14_13_6_7_1_2013 13 90
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 273 3 4 30 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 90 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 90 273 3 3 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 90 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 90 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 273 3 2 30 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 90 273 (Polychromatic418967fa.accept_20_5_10_13_1_6754 5 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 90 273 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 90 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 90 273 3 1 30 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 90 273
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 90 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 90 273 (Polychromatic418967fa.accept_14_1_6_7_1_1936 1 90 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 273
  (allA_succ_of_accept 88 89 273 (accept_3_4 88 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87
  89 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 87 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 86 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 89 273 (accept_3_4 85 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 89 273 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 89 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 83 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 89 273 (accept_3_4 82 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  89 273 (Polychromatic418967fa.accept_19_5_13_7_1_8689 81 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 89 273 (accept_3_4 79 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 89 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 89 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 77 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 89 273 (accept_3_4 76 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  89 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 75 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 273 (accept_3_4 73 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 273 (Polychromatic418967fa.accept_14_2_5_7_1_3767 72 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 89 273
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 71 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 89 273 (accept_3_4 70 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  89 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 273 (accept_3_4 67 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 273 (Polychromatic418967fa.accept_10_6_9_3_1_935 66 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 89 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 65 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 89 273 (accept_3_4 64 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  89 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 273 (accept_3_4 61 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 89 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 59 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 89 273 (accept_3_4 58 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  89 273 (Polychromatic418967fa.accept_22_13_1_9_1_7266 57 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 273 (accept_3_4 55 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 273 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 89 273
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 53 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 89 273 (accept_3_4 52 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  89 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 273 (accept_3_4 49 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 273 (Polychromatic418967fa.accept_17_14_4_1_1_3341 48 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 47 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 273 (accept_3_4 46 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 273 (Polychromatic418967fa.accept_16_13_9_1_1_3022 45 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 273 (accept_3_4 43 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 273 (accept_3_4 40 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 273 (accept_3_4 37 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 273 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 273
  (Polychromatic418967fa.accept_22_13_1_9_1_7266 35 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 273 (accept_3_4 34 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 273 (accept_3_4 31 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 273 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 273 (accept_3_4 28 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 273 (accept_3_4 25 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 273 (accept_3_4 22 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 273 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 273 (accept_3_4 19 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 273 (Polychromatic418967fa.accept_16_2_9_1_1_6404 18 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 273
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 273 (accept_3_4 16 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 273 (accept_3_4 13 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 273 (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 273 (accept_3_4 10 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 273 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 273 (accept_3_4 7 89 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 89 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 273 (accept_3_4 4 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  273 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 89 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 89 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 273 (accept_3_4 1 89 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 88 273 (allA_succ_of_accept 87 88 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 87 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 88 273 (accept_3_5 86 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 85 88 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 88 273
  (Polychromatic418967fa.accept_15_9_13_3_1_535 84 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 88 273 (accept_3_5 83 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  88 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 82 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 88 273 (Polychromatic418967fa.accept_10_1_8_3_1_947 81 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 88 273 (accept_3_5 80 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 88 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 78 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 88 273 (accept_3_5 77 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  88 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 88 273 (Polychromatic418967fa.accept_10_5_8_3_1_229 75 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 88 273 (accept_3_5 74 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 88 273
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 88 273 (accept_3_5 71 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  88 273 (Polychromatic418967fa.accept_15_10_13_3_1_4816 70 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 88 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 88 273 (accept_3_5 68 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 88 273
  (Polychromatic418967fa.accept_10_6_8_3_1_930 66 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 88 273 (accept_3_5 65 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  88 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 88 273 (Polychromatic418967fa.accept_16_15_8_1_1_9959 63 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 88 273 (accept_3_5 62 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 88 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 88 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 60 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 88 273 (accept_3_5 59 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  88 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 88 273 (Polychromatic418967fa.accept_15_12_13_3_1_1915 57 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 88 273 (accept_3_5 56 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 88 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 88 273
  (Polychromatic418967fa.accept_12_6_4_9_1_544 54 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 88 273 (accept_3_5 53 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  88 273 (Polychromatic418967fa.accept_14_10_4_7_1_1214 52 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 88 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 88 273 (accept_3_5 50 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 88 273
  (Polychromatic418967fa.accept_26_22_10_13_1_16737 48 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 88 273 (accept_3_5 47 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 88 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 88 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 273 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 88 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 88 273 (accept_3_5 44 88 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 43
  88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 88 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 88 273 (accept_3_5 41 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  88 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 88 273 (Polychromatic418967fa.accept_14_11_4_7_1_609 39 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 88 273 (accept_3_5 38 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 88 273
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 88 273 (accept_3_5 35 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  88 273 (Polychromatic418967fa.accept_19_15_12_7_1_7227 34 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 88 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 88 273 (accept_3_5 32 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 88 273
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 88 273 (accept_3_5 29 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  88 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 88 273 (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 88 273 (accept_3_5 26 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 88 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 88 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 88 273 (accept_3_5 23 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  88 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 88 273 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 88 273 (accept_3_5 20 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 88 273
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 88 273 (accept_3_5 17 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  88 273 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 88 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 88 273 (accept_3_5 14 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 88 273
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 88 273 (accept_3_5 11 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  88 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 88 273 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 88 273 (accept_3_5 8 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 88 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 88 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 88 273 (accept_3_5 5 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 88
  273 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 88 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 88 273 (Polychromatic418967fa.accept_14_3_4_7_1_175 3 88 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 88 273 (accept_3_5 2 88 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 88 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 88 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 273
  (allA_succ_of_accept 86 87 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 87 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 85 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 87 273 3 28 29 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 87 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 83 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 87 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 87 273 3 27 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 87 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 80
  87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 87 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 79 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 87 273 3 26 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 87 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 87 273 3 25 29 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 87 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 87 273 3 24 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 87 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 71
  87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 70 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 87 273 3 23 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 87 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 87 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 87 273 3 22 29 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 87 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 87 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 87 273 3 21 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 87 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 87
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 87 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 87 273 3 20 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 87 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 87 273 3 19 29 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 87 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 273 3 18 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 53
  87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 87 273 3 17 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 87 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 87 273 3 16 29 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 87 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 87 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 273 3 15 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 44
  87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 87 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 87 273 3 14 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 87 273 3 13 29 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 87 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 273 3 12 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 87 273 3 11 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 87 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 87 273 3 10 29 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 87 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 87 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 273 3 9 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 87 273 3 8 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 87 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 87 273 3 7 29 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 87 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 273 3 6 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 87 273 3 5 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 87 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 87 273 3 4 29 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 87 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 87 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 273 3 3 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 87 273 3 2 29 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 87 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 87 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 87 273 3 1 29 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 87 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 87 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 87 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 87 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 87
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 273
  (allA_succ_of_accept 85 86 273 (accept_3_4 85 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84
  86 273 (Polychromatic418967fa.accept_18_12_14_3_1_2655 84 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 86 273 (accept_3_4 82 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 86 273 (Polychromatic418967fa.accept_15_6_11_3_1_1172 81 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 86 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 80 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 86 273 (accept_3_4 79 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  86 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 86 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 86 273 (accept_3_4 76 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 86 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 74 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 86 273 (accept_3_4 73 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  86 273 (Polychromatic418967fa.accept_22_6_20_9_1_9031 72 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 86 273 (accept_3_4 70 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 86 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 86 273
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 68 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 86 273 (accept_3_4 67 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  86 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 66 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 86 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 86 273 (accept_3_4 64 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 86 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 62 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 86 273 (accept_3_4 61 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  86 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 86 273 (accept_3_4 58 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 86 273 (Polychromatic418967fa.accept_10_7_6_3_1_927 57 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 86 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 86 273 (accept_3_4 55 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  86 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 86 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 86 273 (accept_3_4 52 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 86 273
  (Polychromatic418967fa.accept_16_2_6_1_1_2069 50 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 86 273 (accept_3_4 49 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  86 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 86 273 (accept_3_4 46 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 86 273 (Polychromatic418967fa.accept_18_9_14_3_1_6407 45 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 86 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 44 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 86 273 (accept_3_4 43 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  86 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 86 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 86 273 (accept_3_4 40 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 86 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 86 273 (accept_3_4 37 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  86 273 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 86 273 (accept_3_4 34 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 86 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 86 273
  (Polychromatic418967fa.accept_24_8_14_9_1_9993 32 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 86 273 (accept_3_4 31 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  86 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 86 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 86 273 (accept_3_4 28 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 86 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 86 273 (accept_3_4 25 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  86 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 86 273 (accept_3_4 22 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 86 273 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 86 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 86 273 (accept_3_4 19 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  86 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 86 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 86 273 (accept_3_4 16 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 86 273
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 86 273 (accept_3_4 13 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  86 273 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 86 273 (accept_3_4 10 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 86 273 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 86 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 86 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 86 273 (accept_3_4 7 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 86
  273 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 86 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 86 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 86 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 86 273 (accept_3_4 4 86 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 86 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 86 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 86 273 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 86
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 86 273 (accept_3_4 1 86 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 85 273
  (allA_succ_of_accept 84 85 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 85 273 (accept_3_5 83 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 82 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 85 273 (Polychromatic418967fa.accept_15_6_10_3_1_2844
  81 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 273 (accept_3_5 80
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 79 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 85 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 78 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 85 273 (accept_3_5 77 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 85 273 (Polychromatic418967fa.accept_12_3_1_9_1_202
  75 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 273 (accept_3_5 74
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 73 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 85 273 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 85 273 (accept_3_5 71 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 85 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 69
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 273 (accept_3_5 68 85
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 273
  (Polychromatic418967fa.accept_10_7_5_3_1_542 67 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 85 273 (Polychromatic418967fa.accept_15_6_10_3_1_2844 66 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 85 273 (accept_3_5 65 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 85 273 (Polychromatic418967fa.accept_12_3_1_9_1_202
  63 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 273 (accept_3_5 62
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 61 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 85 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 85 273 (accept_3_5 59 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 85 273 (Polychromatic418967fa.accept_10_7_5_3_1_542
  57 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 273 (accept_3_5 56
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 55 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 85 273 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 273 (accept_3_5 53 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 51
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 273 (accept_3_5 50 85
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 273
  (Polychromatic418967fa.accept_19_11_9_7_1_4447 49 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 85 273 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 273 (accept_3_5 47 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 85 273 (Polychromatic418967fa.accept_16_13_5_1_1_3017
  45 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 273 (accept_3_5 44
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 85 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 273 (accept_3_5 41 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 85 273 (Polychromatic418967fa.accept_12_3_1_9_1_202
  39 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 273 (accept_3_5 38
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 85 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 85 273 (accept_3_5 35 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 33
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 273 (accept_3_5 32 85
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 273
  (Polychromatic418967fa.accept_16_15_5_1_1_7724 31 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 85 273 (Polychromatic418967fa.accept_18_12_13_3_1_6427 30 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 85 273 (accept_3_5 29 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 85 273 (Polychromatic418967fa.accept_10_7_5_3_1_542
  27 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 273 (accept_3_5 26
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 85 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 273 (accept_3_5 23 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 273 (Polychromatic418967fa.accept_11_10_8_9_1_492
  21 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 273 (accept_3_5 20
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 85 273 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 273 (accept_3_5 17 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 85 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 273 (accept_3_5 14 85
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 273
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 85 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 273 (accept_3_5 11 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 85 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 85 273 (Polychromatic418967fa.accept_15_9_10_3_1_2845
  9 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 273 (accept_3_5 8 85
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 273 (Polychromatic418967fa.accept_9_7_4_3_1_204
  7 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 273 (accept_3_5 5 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 85 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 273 (accept_3_5 2 85 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 85 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 273
  (allA_succ_of_accept 83 84 273 (Polychromatic418967fa.accept_15_8_9_3_1_1194 83 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 84 273 (Polychromatic418967fa.accept_11_5_7_9_1_2696 82 84 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 84 273 3 27 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 84 273
  (Polychromatic418967fa.accept_15_5_9_3_1_528 80 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 84 273 (Polychromatic418967fa.accept_10_9_4_3_1_539 79 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 273 3 26 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 84 273 7 11 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 84 273 (Polychromatic418967fa.accept_16_12_4_1_1_1257
  76 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 84 273 3 25 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 84 273
  (Polychromatic418967fa.accept_18_2_12_3_1_2707 74 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 84 273 (Polychromatic418967fa.accept_15_13_9_3_1_1949 73 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 273 3 24 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 273 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  71 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 273 7 10 12 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 84 273 3 23 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 84 273
  (Polychromatic418967fa.accept_11_2_7_9_1_890 68 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 84 273 (Polychromatic418967fa.accept_10_7_4_3_1_560 67 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 273 3 22 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 273 (Polychromatic418967fa.accept_15_5_9_3_1_528 65
  84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 84 273
  (Polychromatic418967fa.accept_22_20_18_9_1_15119 64 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 84 273 21 3 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 84 273 (Polychromatic418967fa.accept_16_14_4_1_1_3049 62 84 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 84 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 61
  84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 273 3 20 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 273
  (Polychromatic418967fa.accept_10_9_4_3_1_539 59 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 84 273 (Polychromatic418967fa.accept_15_13_9_3_1_1949 58 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 84 273 3 19 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 84 273 7 8 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 273 (Polychromatic418967fa.accept_15_10_9_3_1_1947
  55 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 273 3 18 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 273
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 84 273 (Polychromatic418967fa.accept_19_14_8_7_1_12706 52 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 84 273 3 17 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 84 273 (Polychromatic418967fa.accept_15_5_9_3_1_528 50
  84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 84 273 7 7 12 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 84 273 3 16 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 273
  (Polychromatic418967fa.accept_10_7_4_3_1_560 47 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 84 273 (Polychromatic418967fa.accept_11_2_7_9_1_890 46 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 84 273 3 15 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 84 273 (Polychromatic418967fa.accept_16_12_4_1_1_1257
  44 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 84 273
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 273 21 2 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 84 273 (Polychromatic418967fa.accept_22_19_18_9_1_16736 41 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 273 (Polychromatic418967fa.accept_15_10_9_3_1_1947 40 84
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 84 273 3 13 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 84 273
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 38 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 84 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 273 3 12 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 84 273 7 5 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 84 273 (Polychromatic418967fa.accept_19_15_8_7_1_11482
  34 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 84 273 3 11 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 84 273
  (Polychromatic418967fa.accept_17_15_16_1_1_7080 32 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 84 273 (Polychromatic418967fa.accept_18_13_12_3_1_3857 31 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 273 3 10 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 29
  84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 273 7 4 12 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 84 273 3 9 28 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 84 273
  (Polychromatic418967fa.accept_18_8_12_3_1_2708 26 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 84 273 (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 273 3 8 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 273 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 84 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 273
  (Polychromatic418967fa.accept_17_5_16_1_1_3358 22 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 84 273 21 1 4 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 84 273 (Polychromatic418967fa.accept_15_5_9_3_1_528 20 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 84 273 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 84 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 273 3 6 28 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 273
  (Polychromatic418967fa.accept_10_7_4_3_1_560 17 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 84 273 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 84 273 3 5 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 84 273 7 2 12 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 84 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 273 3 4 28 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 273
  (Polychromatic418967fa.accept_19_11_8_7_1_11423 11 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 84 273 (Polychromatic418967fa.accept_15_10_9_3_1_1947 10 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 84 273 3 3 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 84 273 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 84 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 84 273 7 1 12 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 84 273 3 2 28 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 273
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 84 273 (Polychromatic418967fa.accept_29_4_26_12_1_16735 4 84 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 84 273 3 1 28 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 84 273 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 84 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 273
  (Polychromatic418967fa.accept_18_1_12_3_1_6426 1 84 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 273
  (allA_succ_of_accept 82 83 273 (accept_3_4 82 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81
  83 273 (Polychromatic418967fa.accept_20_1_3_13_1_8217 81 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 83 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 83 273 (accept_3_4 79 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 83 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 83 273 (accept_3_4 76 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  83 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 75 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 83 273 (accept_3_4 73 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 83 273 (Polychromatic418967fa.accept_15_12_8_3_1_1995 72 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 83 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 71 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 83 273 (accept_3_4 70 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  83 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 83 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 83 273 (accept_3_4 67 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 83 273
  (Polychromatic418967fa.accept_15_5_8_3_1_556 65 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 83 273 (accept_3_4 64 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  83 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 273 (accept_3_4 61 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 273 (accept_3_4 58 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 273 (Polychromatic418967fa.accept_14_1_13_7_1_1205 57 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 273 (accept_3_4 55 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 273 (accept_3_4 52 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 273 (accept_3_4 49 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 273 (Polychromatic418967fa.accept_14_6_13_7_1_2015 48 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 273
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 273 (accept_3_4 46 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 273 (Polychromatic418967fa.accept_16_13_3_1_1_2100 45 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 273 (accept_3_4 43 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 273 (accept_3_4 40 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 273 (accept_3_4 37 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 273 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 273 (accept_3_4 34 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 273 (accept_3_4 31 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 273
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 29 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 273 (accept_3_4 28 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 273 (accept_3_4 25 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 273 (accept_3_4 22 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 273 (Polychromatic418967fa.accept_20_1_3_13_1_8217 21 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 273 (accept_3_4 19 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 273 (accept_3_4 16 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 273 (accept_3_4 13 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 273 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 273
  (Polychromatic418967fa.accept_15_11_8_3_1_1943 11 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 273 (accept_3_4 10 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 273 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 273 (accept_3_4 7 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 83 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 273 (accept_3_4 4 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  273 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 83 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 83 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 273 (accept_3_4 1 83 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 83
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 273
  (allA_succ_of_accept 81 82 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 81 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 82 273 (accept_3_5 80 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 82 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 78
  82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 82 273 (accept_3_5 77 82
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 82 273
  (Polychromatic418967fa.accept_9_4_1_3_1_190 76 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 82 273 (accept_3_5 74 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 82 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 82 273 (Polychromatic418967fa.accept_14_2_12_7_1_617
  72 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 82 273 (accept_3_5 71
  82 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 82 273
  (Polychromatic418967fa.accept_9_7_1_3_1_443 70 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 82 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 82 273 (accept_3_5 68 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 82 273 (Polychromatic418967fa.accept_12_6_10_9_1_531
  66 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 82 273 (accept_3_5 65
  82 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 82 273
  (Polychromatic418967fa.accept_15_4_7_3_1_119 64 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 273 (accept_3_5 62 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 82 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 60
  82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 273 (accept_3_5 59 82
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 273
  (Polychromatic418967fa.accept_9_4_1_3_1_190 58 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 82 273 (Polychromatic418967fa.accept_15_12_7_3_1_1940 57 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 273 (accept_3_5 56 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 273 (Polychromatic418967fa.accept_12_6_10_9_1_531
  54 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 273 (accept_3_5 53
  82 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 273
  (Polychromatic418967fa.accept_9_7_1_3_1_443 52 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 273 (accept_3_5 50 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 82 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 273
  (Polychromatic418967fa.accept_22_4_16_9_1_10639 48 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 273 (accept_3_5 47 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 273 (Polychromatic418967fa.accept_19_8_6_7_1_7216 46 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 273 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 273 (accept_3_5 44 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 273
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 273 (accept_3_5 41 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 273 (accept_3_5 38 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 82 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 273
  (Polychromatic418967fa.accept_26_10_4_13_1_16734 36 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 82 273 (accept_3_5 35 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 82 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 82 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 82 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 273 (accept_3_5 32 82 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 273
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 273 (accept_3_5 29 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 273 (Polychromatic418967fa.accept_16_12_2_1_1_1215 28 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 273 (accept_3_5 26 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 82 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 273
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 273 (accept_3_5 23 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 273 (accept_3_5 20 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 273
  (Polychromatic418967fa.accept_11_7_5_9_1_884 18 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 273 (accept_3_5 17 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 273 (accept_3_5 14 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 82 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 273
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 273 (accept_3_5 11 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 273 (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 273 (Polychromatic418967fa.accept_14_9_12_7_1_597 9 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 273 (accept_3_5 8 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 273
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 273 (accept_3_5 5 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  273 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 82 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 82 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 273 (accept_3_5 2 82 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 82 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 82 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 273
  (allA_succ_of_accept 80 81 273 (Polychromatic418967fa.accept_14_10_11_7_1_1955 80 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 81 273 (Polychromatic418967fa.accept_11_2_4_9_1_484 79 81 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 81 273 3 26 27 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 81 273
  (Polychromatic418967fa.accept_23_8_12_20_1_16733 77 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 81 273 (Polychromatic418967fa.accept_15_1_6_3_1_2827 76 81 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 81 273 3 25 27 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 81 273
  (Polychromatic418967fa.accept_14_4_11_7_1_1234 74 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 273 (Polychromatic418967fa.accept_14_3_11_7_1_1260 73 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 81 273 3 24 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 81 273 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  71 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 273
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 70 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 81 273 3 23 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 81 273 (Polychromatic418967fa.accept_10_8_1_3_1_1374 68 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 81 273 (Polychromatic418967fa.accept_18_13_9_3_1_5114 67 81
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 81 273 3 22 27 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 81 273
  (Polychromatic418967fa.accept_15_5_6_3_1_525 65 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 81 273 (Polychromatic418967fa.accept_22_20_15_9_1_15148 64 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 81 273 3 21 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 81 273 (Polychromatic418967fa.accept_10_2_1_3_1_233 62
  81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 273
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 61 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 81 273 3 20 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 81 273 (Polychromatic418967fa.accept_14_3_11_7_1_1260 59 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 273 (Polychromatic418967fa.accept_10_8_1_3_1_1374 58 81 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 273 3 19 27 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 273
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 56 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 273 (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 81 273 3 18 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 81 273 (Polychromatic418967fa.accept_17_2_13_1_1_3355
  53 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 273
  (Polychromatic418967fa.accept_10_2_1_3_1_233 52 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 81 273 3 17 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 81 273 (Polychromatic418967fa.accept_15_5_6_3_1_525 50 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 273 (Polychromatic418967fa.accept_18_13_9_3_1_5114 49 81
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 273 3 16 27 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 273
  (Polychromatic418967fa.accept_19_9_5_7_1_5853 47 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 81 273 (Polychromatic418967fa.accept_11_2_4_9_1_484 46 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 81 273 3 15 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 81 273 (Polychromatic418967fa.accept_18_8_9_3_1_2645
  44 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 273
  (Polychromatic418967fa.accept_18_7_9_3_1_800 43 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 81 273 3 14 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 81 273 (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 273 (Polychromatic418967fa.accept_15_10_6_3_1_1160 40 81
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 273 3 13 27 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 273
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 38 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 273 (Polychromatic418967fa.accept_18_1_9_3_1_2672 37 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 81 273 3 12 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 81 273 (Polychromatic418967fa.accept_11_2_4_9_1_484 35
  81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 273
  (Polychromatic418967fa.accept_20_14_1_13_1_8286 34 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 81 273 3 11 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 81 273 (Polychromatic418967fa.accept_10_2_1_3_1_233 32 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 273 (Polychromatic418967fa.accept_14_3_11_7_1_1260 31 81
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 273 3 10 27 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 273
  (Polychromatic418967fa.accept_17_12_13_1_1_4478 29 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 81 273 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 81 273 3 9 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 81 273 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 81 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 273
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 81 273 3 8 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 81 273 (Polychromatic418967fa.accept_20_3_1_13_1_6742 23 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 273 (Polychromatic418967fa.accept_10_2_1_3_1_233 22 81 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 273 3 7 27 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 273
  (Polychromatic418967fa.accept_15_5_6_3_1_525 20 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 273 (Polychromatic418967fa.accept_17_2_13_1_1_3355 19 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 81 273 3 6 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 81 273 (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 81 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 273
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 81 273 3 5 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 81 273 (Polychromatic418967fa.accept_17_14_13_1_1_3356 14 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 273 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 81 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 273 3 4 27 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 273
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 81 273 (Polychromatic418967fa.accept_14_10_11_7_1_1955 10 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 81 273 3 3 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 81 273 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 81 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 273
  (Polychromatic418967fa.accept_18_7_9_3_1_800 7 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 81 273 3 2 27 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 81 273 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 273 (Polychromatic418967fa.accept_14_4_11_7_1_1234 4 81 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 273 3 1 27 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 273
  (Polychromatic418967fa.accept_10_2_1_3_1_233 2 81 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 81 273 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 81 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 81
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 273
  (allA_succ_of_accept 79 80 273 (accept_3_4 79 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  80 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 78 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 80 273 (accept_3_4 76 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 80 273 (Polychromatic418967fa.accept_23_6_11_20_1_16732 75 80 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 80 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 74 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 80 273 (accept_3_4 73 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  80 273 (Polychromatic418967fa.accept_11_6_3_9_1_906 72 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 80 273 (accept_3_4 70 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 80 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 69 80 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 80 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 68 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 80 273 (accept_3_4 67 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  80 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 66 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 80 273 (accept_3_4 64 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 80 273 (Polychromatic418967fa.accept_18_9_8_3_1_2702 63 80 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 80 273
  (Polychromatic418967fa.accept_15_2_5_3_1_552 62 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 80 273 (accept_3_4 61 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  80 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 80 273 (accept_3_4 58 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 80 273 (Polychromatic418967fa.accept_17_6_12_1_1_7043 57 80 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 80 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 80 273 (accept_3_4 55 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  80 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 80 273 (accept_3_4 52 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 80 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 80 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 80 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 80 273 (accept_3_4 49 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  80 273 (Polychromatic418967fa.accept_18_12_8_3_1_1627 48 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 80 273 (accept_3_4 46 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 80 273 (Polychromatic418967fa.accept_14_3_10_7_1_3773 45 80 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 80 273
  (Polychromatic418967fa.accept_24_20_8_9_1_8282 44 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 80 273 (accept_3_4 43 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  80 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 80 273 (accept_3_4 40 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 80 273 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 80 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 80 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 80 273 (accept_3_4 37 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  80 273 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 80 273 (accept_3_4 34 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 80 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 80 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 80 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 80 273 (accept_3_4 31 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  80 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 80 273 (accept_3_4 28 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 80 273 (Polychromatic418967fa.accept_18_9_8_3_1_2702 27 80 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 80 273
  (Polychromatic418967fa.accept_28_26_24_21_1_16731 26 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 80 273 (accept_3_4 25 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 80 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 80 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 80 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 80 273 (accept_3_4 22 80 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 80 273 (Polychromatic418967fa.accept_15_6_5_3_1_1988
  21 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 80 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 80 273 (accept_3_4 19 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  80 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 80 273 (accept_3_4 16 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 80 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 80 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 80 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 80 273 (accept_3_4 13 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  80 273 (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 80 273 (accept_3_4 10 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 80 273 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 80 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 80 273
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 80 273 (accept_3_4 7 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 80
  273 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 80 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 80 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 80 273 (accept_3_4 4 80 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 80 273 (Polychromatic418967fa.accept_14_3_10_7_1_3773 3 80 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 80 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  80 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 80 273 (accept_3_4 1 80 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 79 273
  (allA_succ_of_accept 78 79 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 79 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 79 273 (accept_3_5 77 79 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 79 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 79 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  75 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 273 (accept_3_5 74
  79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 273
  (Polychromatic418967fa.accept_9_1_7_3_1_41 73 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 79 273 (Polychromatic418967fa.accept_14_2_9_7_1_5633 72 79 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 79 273 (accept_3_5 71 79 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 79 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 79 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 69
  79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 273 (accept_3_5 68 79
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 273 (Polychromatic418967fa.accept_9_4_7_3_1_43
  67 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 273 (accept_3_5 65 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 273 (accept_3_5 62 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 273 (Polychromatic418967fa.accept_14_5_9_7_1_590 61 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 60 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 273 (accept_3_5 59 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 273 (Polychromatic418967fa.accept_23_11_10_20_1_13526 57 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 273 (accept_3_5 56 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 79 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 273 (accept_3_5 53 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 273 (accept_3_5 50 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 273
  (Polychromatic418967fa.accept_11_4_2_9_1_496 48 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 273 (accept_3_5 47 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 273 (Polychromatic418967fa.accept_18_9_7_3_1_3871 45 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 273 (accept_3_5 44 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 273 (Polychromatic418967fa.accept_16_11_15_1_1_2074 43 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 273 (accept_3_5 41 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 273 (accept_3_5 38 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 273
  (Polychromatic418967fa.accept_10_6_9_3_1_935 36 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 273 (accept_3_5 35 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 273 (accept_3_5 32 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 273 (accept_3_5 29 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 273 (accept_3_5 26 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 273 (Polychromatic418967fa.accept_17_8_11_1_1_5761 25 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 273 (accept_3_5 23 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 273 (Polychromatic418967fa.accept_16_5_15_1_1_2113 21 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 273 (accept_3_5 20 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 79 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 273 (accept_3_5 17 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 273 (accept_3_5 14 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 273
  (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 273 (accept_3_5 11 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 273 (Polychromatic418967fa.accept_18_9_7_3_1_3871 9 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 273 (accept_3_5 8 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 273 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 79 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 273 (accept_3_5 5 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 79 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 79 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 273 (accept_3_5 2 79 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 79 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 273
  (allA_succ_of_accept 77 78 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 78 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 76 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 78 273 3 25 26 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 78 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 74 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 78 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 273 3 24 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 71
  78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 78 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 70 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 78 273 3 23 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 68 78 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 78 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 273 3 22 26 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 78 273 13 5 6 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 78 273
  (Polychromatic418967fa.accept_9_1_6_3_1_177 64 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 78 273 3 21 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 78 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 62 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 78 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 273 3 20 26 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 78 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 78 273 3 19 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 78 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 78 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 78 273 3 18 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 78 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 273 13 4 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 78 273 3 17 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 78 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 78 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 273 3 16 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 78 273 3 15 26 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 78 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 78 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 273 3 14 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 78 273 39 1 2 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 78 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 78 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 273 3 12 26 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 78 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 78 273 3 11 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 78 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 78 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 273 3 10 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 78 273 3 9 26 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 273 13 2 6 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 273 3 8 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 78 273 3 7 26 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 78 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 78 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 273 3 6 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 78 273 3 5 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 78 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 78 273 13 1 6 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 78 273 3 4 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 273
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 78 273 3 3 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 78 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 273 3 2 26 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 273
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 78 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 78 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 78 273 3 1 26 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 78 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 78 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 273
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 78 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 273
  (allA_succ_of_accept 76 77 273 (accept_3_4 76 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 273 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 77 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 273 (accept_3_4 73 77 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 273 (Polychromatic418967fa.accept_15_12_2_3_1_1146 72 77 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 71 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 77 273 7 10 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 77 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 77 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 77 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 273 (accept_3_4 67 77 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 273 (Polychromatic418967fa.accept_10_6_7_3_1_547
  66 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 65 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 273 (accept_3_4 64 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 77
  273 7 9 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62
  77 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 77 273 (accept_3_4 61 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 77 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 77 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 273 (Polychromatic418967fa.accept_15_14_2_3_1_1980 59 77
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 273 (accept_3_4 58 77 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 77 273 (Polychromatic418967fa.accept_15_12_2_3_1_1146
  57 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 77 273 7 8 11 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 77 273 (accept_3_4 55
  77 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 273
  (Polychromatic418967fa.accept_10_4_7_3_1_54 54 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 77 273 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 77 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 77 273 (accept_3_4 52 77 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 77 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 77 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 77 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 50
  77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 77 273 7 7 11 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 77 273
  (Polychromatic418967fa.accept_19_10_1_7_1_10040 48 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 77 273 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 77 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 77 273 (accept_3_4 46 77 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 77 273 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 77 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 77 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 44
  77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 273 (accept_3_4 43 77
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 77 273 7 6 11 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 77 273
  (Polychromatic418967fa.accept_16_9_13_1_1_3069 41 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 273 (accept_3_4 40 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 77 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 273 (accept_3_4 37 77 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 77 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 77 273 7 5 11 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 77 273 (accept_3_4 34 77 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 77 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 77 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 273
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 77 273 (accept_3_4 31 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  77 273 (Polychromatic418967fa.accept_16_14_13_1_1_5278 30 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 77 273 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 77 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 77 273 7 4 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 77 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 27
  77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 273
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 77 273 (accept_3_4 25 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  77 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 273 (Polychromatic418967fa.accept_19_4_1_7_1_4438 23 77 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 273 (accept_3_4 22 77 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77 273 7 3 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 77 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 77 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 273 (accept_3_4 19 77 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 273 (Polychromatic418967fa.accept_19_18_1_7_1_14104 18 77
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 273 (accept_3_4 16 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 77 273 7 2 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 77 273 (accept_3_4 13 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 77 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 77 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 273 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 77 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 273 (accept_3_4 10 77 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 273 (Polychromatic418967fa.accept_16_9_13_1_1_3069
  9 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 273
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 77 273 7 1 11 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 77 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 77 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 273 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 77 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 273 (accept_3_4 4 77 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 3
  77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 273
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 273 (accept_3_4 1 77 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 76 273
  (allA_succ_of_accept 75 76 273 (Polychromatic418967fa.accept_16_11_12_1_1_3001 75 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 76 273 (accept_3_5 74 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 76 273 (Polychromatic418967fa.accept_16_8_12_1_1_7720
  72 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 76 273 (accept_3_5 71
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 76 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 70 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 76 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 273 (accept_3_5 68 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 273 (Polychromatic418967fa.accept_12_6_4_9_1_544
  66 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 273 (accept_3_5 65
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 64 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 76 273 (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 76 273 (accept_3_5 62 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 76 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 60
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 273 (accept_3_5 59 76
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 273
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 76 273 (Polychromatic418967fa.accept_10_7_6_3_1_927 57 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 76 273 (accept_3_5 56 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 76 273 (Polychromatic418967fa.accept_12_6_4_9_1_544
  54 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 273 (accept_3_5 53
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 52 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 76 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 76 273 (accept_3_5 50 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 76 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  48 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 273 (accept_3_5 47
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 46 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 76 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 76 273 (accept_3_5 44 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 76 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 42
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 273 (accept_3_5 41 76
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 273
  (Polychromatic418967fa.accept_16_8_12_1_1_7720 40 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 76 273 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 76 273 (accept_3_5 38 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 76 273 (Polychromatic418967fa.accept_14_8_6_7_1_1934
  36 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 273 (accept_3_5 35
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 34 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 76 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 76 273 (accept_3_5 32 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 76 273 (Polychromatic418967fa.accept_11_8_10_9_1_1401
  30 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 273 (accept_3_5 29
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 28 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 76 273 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 76 273 (accept_3_5 26 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 76 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 24
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 273 (accept_3_5 23 76
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 273
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 22 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 76 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 76 273 (accept_3_5 20 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 76 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  18 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 273 (accept_3_5 17
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 16 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 76 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 76 273 (accept_3_5 14 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 76 273 (Polychromatic418967fa.accept_11_1_10_9_1_871
  12 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 273 (accept_3_5 11
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 10 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 76 273 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 76 273 (accept_3_5 8 76 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 76 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 76 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 76 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 6
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 273 (accept_3_5 5 76 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 76 273 (Polychromatic418967fa.accept_15_4_1_3_1_1922 4
  76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 273
  (Polychromatic418967fa.accept_20_3_16_13_1_8307 3 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 76 273 (accept_3_5 2 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76
  273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 76 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 273
  (allA_succ_of_accept 74 75 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 73 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 75 273 3 24 25 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 75 273
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 71 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 75 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 75 273 3 23 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 75 273 (Polychromatic418967fa.accept_10_8_5_3_1_543 68
  75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 273
  (Polychromatic418967fa.accept_10_7_5_3_1_542 67 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 273 3 22 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 65 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 273 (Polychromatic418967fa.accept_24_16_3_9_1_13475 64 75
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 273 3 21 25 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 273 3 20 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  59 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 273 3 19 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 273 (Polychromatic418967fa.accept_23_10_6_20_1_16730 56 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 273 3 18 25 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 273
  (Polychromatic418967fa.accept_12_5_3_9_1_541 53 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 273 (Polychromatic418967fa.accept_10_2_5_3_1_1408 52 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 273 3 17 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 75
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 273
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 75 273 3 16 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 75 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 47 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 273 3 15 25 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 273
  (Polychromatic418967fa.accept_14_2_5_7_1_3767 44 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 43 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 273 3 14 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 41
  75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 273
  (Polychromatic418967fa.accept_14_12_5_7_1_2010 40 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 75 273 3 13 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 75 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 75 273 3 12 25 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 75 273
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 75 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 273 3 11 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 273 (Polychromatic418967fa.accept_10_2_5_3_1_1408
  32 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 273
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 75 273 3 10 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 75 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 273 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 75 273 3 9 25 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 75 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 273 3 8 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 75 273 3 7 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 75 273 (Polychromatic418967fa.accept_19_1_18_7_1_12744 20 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 75 273 3 6 25 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 75 273
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 273 (Polychromatic418967fa.accept_14_2_5_7_1_3767 16 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 273 3 5 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 273
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 75 273 3 4 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 75 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 75 273 3 3 25 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 75 273
  (Polychromatic418967fa.accept_10_8_5_3_1_543 8 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 273 3 2 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 273
  (Polychromatic418967fa.accept_26_4_23_13_1_16729 4 75 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 75 273 3 1 25 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 75 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 75 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 75 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 273 (allA_succ_of_accept
  73 74 273 (accept_3_4 73 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 74 273
  (Polychromatic418967fa.accept_19_15_17_7_1_8734 72 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 74 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 74 273 (accept_3_4 70 74 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 74 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 74 273 (Polychromatic418967fa.accept_9_5_2_3_1_194 68
  74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 74 273 (accept_3_4 67 74
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 74 273
  (Polychromatic418967fa.accept_12_6_2_9_1_537 66 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 74 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 74 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 74 273 (accept_3_4 64 74 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 74 273 (Polychromatic418967fa.accept_9_8_2_3_1_447 62
  74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 74 273 (accept_3_4 61 74
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 74 273
  (Polychromatic418967fa.accept_9_6_2_3_1_771 60 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 74 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 74 273 (accept_3_4 58 74 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 74 273 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 74 273
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 56 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 74 273 (accept_3_4 55 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  74 273 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 74 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 74 273 (accept_3_4 52 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 74 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 74 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 74 273 (accept_3_4 49 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  74 273 (Polychromatic418967fa.accept_18_12_2_3_1_6414 48 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 74 273 (accept_3_4 46 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 74 273 (Polychromatic418967fa.accept_14_3_4_7_1_175 45 74 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 74 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 74 273 (accept_3_4 43 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  74 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 74 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 74 273 (accept_3_4 40 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 74 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 74 273
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 38 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 74 273 (accept_3_4 37 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  74 273 (Polychromatic418967fa.accept_17_2_6_1_1_8357 36 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 74 273 (accept_3_4 34 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 74 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 74 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 74 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 74 273 (accept_3_4 31 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  74 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 74 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 74 273 (accept_3_4 28 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 74 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 74 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 74 273 (accept_3_4 25 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  74 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 74 273 (accept_3_4 22 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 74 273 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 74 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 74 273
  (Polychromatic418967fa.accept_17_3_6_1_1_8382 20 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 74 273 (accept_3_4 19 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  74 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 74 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 74 273 (accept_3_4 16 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 74 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 74 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 74 273 (accept_3_4 13 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  74 273 (Polychromatic418967fa.accept_17_12_6_1_1_4517 12 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 74 273 (accept_3_4 10 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 74 273 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 74 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 74 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 74 273 (accept_3_4 7 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 74
  273 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 74 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 74 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 74 273 (accept_3_4 4 74 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 74 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 74 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 74 273 (Polychromatic418967fa.accept_15_2_14_3_1_1916
  2 74 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 74 273 (accept_3_4 1 74
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 273 (allA_succ_of_accept
  72 73 273 (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 73 273 (accept_3_5 71 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 73 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 73 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 273 (accept_3_5 68 73 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 67
  73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 273
  (Polychromatic418967fa.accept_14_10_3_7_1_1975 66 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 273 (accept_3_5 65 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 63 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 273 (accept_3_5 62 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 73 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 273
  (Polychromatic418967fa.accept_9_6_1_3_1_191 60 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 273 (accept_3_5 59 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 273 (Polychromatic418967fa.accept_11_2_7_9_1_890 57 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 273 (accept_3_5 56 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 273 (Polychromatic418967fa.accept_15_10_13_3_1_4816 55 73 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 273
  (Polychromatic418967fa.accept_15_9_13_3_1_535 54 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 273 (accept_3_5 53 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 273 (accept_3_5 50 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 73 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 273
  (Polychromatic418967fa.accept_18_12_1_3_1_7843 48 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 273 (accept_3_5 47 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 273 (Polychromatic418967fa.accept_16_13_9_1_1_3022 45 73 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 273 (accept_3_5 44 73 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 73 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 273
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 273 (accept_3_5 41 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 273 (accept_3_5 38 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 273 (Polychromatic418967fa.accept_16_5_9_1_1_2070 37 73 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 273
  (Polychromatic418967fa.accept_19_17_16_7_1_7213 36 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 273 (accept_3_5 35 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 273 (accept_3_5 32 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 73 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 273
  (Polychromatic418967fa.accept_18_12_1_3_1_7843 30 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 273 (accept_3_5 29 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 273 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 273 (accept_3_5 26 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 73 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 273
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 273 (accept_3_5 23 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 273 (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 273 (accept_3_5 20 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 273 (Polychromatic418967fa.accept_23_19_4_20_1_10394 19 73 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 273
  (Polychromatic418967fa.accept_14_4_3_7_1_3702 18 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 273 (accept_3_5 17 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 273 (accept_3_5 14 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 73 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 273
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 273 (accept_3_5 11 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 273 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 273 (accept_3_5 8 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 73 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 273
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 273 (accept_3_5 5 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 73 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 73 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 273 (accept_3_5 2 73 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 273 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 73 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 273 (allA_succ_of_accept 71
  72 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 71 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 72 273 (Polychromatic418967fa.accept_19_13_15_7_1_5843 70 72 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 72 273 3 23 24 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 72 273
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 68 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 72 273 (Polychromatic418967fa.accept_15_7_12_3_1_1137 67 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 273 3 22 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 273 (Polychromatic418967fa.accept_10_5_2_3_1_239 65
  72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 273
  (Polychromatic418967fa.accept_22_20_6_9_1_16728 64 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 72 273 3 21 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 72 273 (Polychromatic418967fa.accept_15_2_12_3_1_1183 62 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 72 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 61 72 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 273 3 20 24 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 273
  (Polychromatic418967fa.accept_17_8_4_1_1_5730 59 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 72 273 (Polychromatic418967fa.accept_11_3_6_9_1_1378 58 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 72 273 3 19 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 72 273 (Polychromatic418967fa.accept_17_5_4_1_1_3369
  56 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 72 273
  (Polychromatic418967fa.accept_10_5_2_3_1_239 55 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 273 3 18 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 273 (Polychromatic418967fa.accept_15_8_12_3_1_1912 53 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 273 (Polychromatic418967fa.accept_15_7_12_3_1_1137 52 72
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 72 273 3 17 24 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 72 273
  (Polychromatic418967fa.accept_19_12_15_7_1_11432 50 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 72 273 (Polychromatic418967fa.accept_19_11_15_7_1_3177 49 72 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 273 3 16 24 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 273
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 72 273 (Polychromatic418967fa.accept_19_8_15_7_1_323 46 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 72 273 3 15 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 72 273 (Polychromatic418967fa.accept_16_12_8_1_1_5270
  44 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 72 273
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 43 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 273 3 14 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 72 273 (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 72
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 72 273 3 13 24 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 72 273
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 38 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 72 273 (Polychromatic418967fa.accept_14_9_2_7_1_1242 37 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 273 3 12 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 273 (Polychromatic418967fa.accept_10_5_2_3_1_239 35
  72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 72 273
  (Polychromatic418967fa.accept_26_8_20_13_1_16727 34 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 72 273 3 11 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 72 273 (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 72 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 273
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 273 3 10 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 72 273 (Polychromatic418967fa.accept_23_6_3_20_1_6957 29 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 72 273 (Polychromatic418967fa.accept_15_13_12_3_1_1180 28 72
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 72 273 3 9 24 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 72 273
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 26 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 72 273 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 273 3 8 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 273 (Polychromatic418967fa.accept_14_9_2_7_1_1242 23 72 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 72 273
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 22 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 72 273 3 7 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 72 273 (Polychromatic418967fa.accept_16_4_8_1_1_5257 20 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 273 (Polychromatic418967fa.accept_14_5_2_7_1_2804 19 72 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 273 3 6 24 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 273
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 72 273 (Polychromatic418967fa.accept_22_16_6_9_1_12085 16 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 72 273 3 5 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 72 273 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 72 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 273
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 273 3 4 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 72 273 (Polychromatic418967fa.accept_20_10_12_13_1_8268 10 72
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 72 273 3 3 24 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 72 273
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 72 273 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 273 3 2 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 273 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 72 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72 273
  (Polychromatic418967fa.accept_16_4_8_1_1_5257 4 72 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 72 273 3 1 24 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 72 273 (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 72 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 72 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 72 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 273 (allA_succ_of_accept 70
  71 273 (accept_3_4 70 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 273
  (Polychromatic418967fa.accept_9_6_8_3_1_183 69 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 273 (accept_3_4 67 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 65
  71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 273 (accept_3_4 64 71
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 273
  (Polychromatic418967fa.accept_12_3_11_9_1_193 63 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 273 (accept_3_4 61 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 71 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 273 (Polychromatic418967fa.accept_9_5_8_3_1_437 59
  71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 273 (accept_3_4 58 71
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 273
  (Polychromatic418967fa.accept_17_6_3_1_1_7011 57 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 71 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 273 (accept_3_4 55 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 273 (Polychromatic418967fa.accept_15_8_11_3_1_3847
  53 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 273 (accept_3_4 52
  71 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 273
  (Polychromatic418967fa.accept_9_6_8_3_1_183 51 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 273 (accept_3_4 49 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 71 273 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 47
  71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 273 (accept_3_4 46 71
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 273
  (Polychromatic418967fa.accept_22_1_5_9_1_4114 45 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 71 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 273 (accept_3_4 43 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 273 (Polychromatic418967fa.accept_9_5_8_3_1_437 41
  71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 273 (accept_3_4 40 71
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 273
  (Polychromatic418967fa.accept_12_3_11_9_1_193 39 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 273 (accept_3_4 37 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 71 273 (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 273
  (Polychromatic418967fa.accept_20_15_11_13_1_11192 35 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 71 273 (accept_3_4 34 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 71 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 71 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 273 (accept_3_4 31 71 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 273 (accept_3_4 28 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 273 (accept_3_4 25 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 71 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 273 (accept_3_4 22 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 273 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 273 (accept_3_4 19 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 71 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 273
  (Polychromatic418967fa.accept_23_17_2_20_1_13543 17 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 71 273 (accept_3_4 16 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 71 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 71 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 71 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 273 (accept_3_4 13 71 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 273 (Polychromatic418967fa.accept_10_2_1_3_1_233
  12 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 273 (accept_3_4 10 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 273 (Polychromatic418967fa.accept_17_9_3_1_1_2275 9 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 273 (accept_3_4 7 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 71 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 273 (accept_3_4 4 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  273 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 71 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 71 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 273 (accept_3_4 1 71 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 71 273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 70 273 (allA_succ_of_accept 69 70 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 70 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 70 273 (accept_3_5 68 70 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 70 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 70 273
  (Polychromatic418967fa.accept_12_6_10_9_1_531 66 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 70 273 (accept_3_5 65 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  70 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 70 273 7 9 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 70 273 (accept_3_5 62 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 70 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 70 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 70 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 70 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 70 273 (accept_3_5 59 70 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 58
  70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 273
  (Polychromatic418967fa.accept_11_2_4_9_1_484 57 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 70 273 7 8 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 70 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 70 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 70 273 (Polychromatic418967fa.accept_12_6_10_9_1_531 54 70 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 70 273 (accept_3_5 53 70 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 70 273 (Polychromatic418967fa.accept_15_7_10_3_1_2891
  52 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 70 273 (accept_3_5 50 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 70
  273 7 7 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48
  70 273 (Polychromatic418967fa.accept_27_21_16_3_1_16726 48 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 70 273 (accept_3_5 47 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 70 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 70 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 70 273 (Polychromatic418967fa.accept_20_5_10_13_1_6754 45 70
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 70 273 (accept_3_5 44 70 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 273 7 6 10 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 273 (accept_3_5 41
  70 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 70 273
  (Polychromatic418967fa.accept_9_4_7_3_1_43 40 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 70 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 70 273 (accept_3_5 38 70 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 70 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 70 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 273 (Polychromatic418967fa.accept_15_6_10_3_1_2844
  36 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 70 273 7 5 10 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 70 273
  (Polychromatic418967fa.accept_16_2_6_1_1_2069 34 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 70 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 70 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 273 (accept_3_5 32 70 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 70 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 70 273 (Polychromatic418967fa.accept_12_6_10_9_1_531
  30 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 70 273 (accept_3_5 29
  70 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 273 7 4 10 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 273 (accept_3_5 26 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  70 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 70 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 70 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 70 273 (accept_3_5 23 70 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 70 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 70 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 70 273 7 3 10 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 70 273 (accept_3_5 20 70 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 70 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 70 273
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 70 273 (accept_3_5 17 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  70 273 (Polychromatic418967fa.accept_17_16_2_1_1_4492 16 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 70 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 70 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 273 7 2 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 273
  (Polychromatic418967fa.accept_20_12_10_13_1_9747 12 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 70 273 (accept_3_5 11 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 70 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 70 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 70 273 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 70 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 70 273 (accept_3_5 8 70 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 70 273 7 1 10 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 70 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 70
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 70 273 (accept_3_5 5 70 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 70 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 70
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 273 (accept_3_5 2 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 70 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 273
  (allA_succ_of_accept 68 69 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 68 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 69 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 273 3 22 23 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 69 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 69 273 3 21 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 69 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 69 273 3 20 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 58 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 273 3 19 23 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 273 3 18 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 53
  69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 52 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 69 273 3 17 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 69 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 69 273 3 16 23 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 69 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 69 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 273 3 15 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 44
  69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 69 273 3 14 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 69 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 69 273 3 13 23 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 69 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 273 3 12 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 69 273 3 11 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 69 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 273 3 10 23 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 273 3 9 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 273 3 8 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 273 3 7 23 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 20 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 273 3 6 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 273 3 5 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 273 3 4 23 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 273 3 3 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 273 3 2 23 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 69 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 273 3 1 23 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 69 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 69 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 273 (allA_succ_of_accept 67 68 273 (accept_3_4 67 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 68 273 (Polychromatic418967fa.accept_10_6_8_3_1_930 66 68 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 68 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 68 273 (accept_3_4 64 68 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 68 273 (Polychromatic418967fa.accept_18_9_14_3_1_6407
  63 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 68 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 62 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 68 273 (accept_3_4 61 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  68 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 68 273 (accept_3_4 58 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 68 273 (Polychromatic418967fa.accept_15_12_8_3_1_1995 57 68 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 68 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 68 273 (accept_3_4 55 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  68 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 54 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 68 273 (accept_3_4 52 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 68 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 68 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 68 273
  (Polychromatic418967fa.accept_15_5_8_3_1_556 50 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 68 273 (accept_3_4 49 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  68 273 (Polychromatic418967fa.accept_11_4_2_9_1_496 48 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 68 273 (accept_3_4 46 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 68 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 68 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 68 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 44 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 68 273 (accept_3_4 43 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  68 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 68 273 (accept_3_4 40 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 68 273 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 68 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 68 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 68 273 (accept_3_4 37 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  68 273 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 68 273 (accept_3_4 34 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 68 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 68 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 68 273
  (Polychromatic418967fa.accept_19_13_11_7_1_4451 32 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 68 273 (accept_3_4 31 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  68 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 68 273 (accept_3_4 28 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 68 273 (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 68 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 68 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 68 273 (accept_3_4 25 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  68 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 68 273 (accept_3_4 22 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 68 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 68 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 68 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 68 273 (accept_3_4 19 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  68 273 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 68 273 (accept_3_4 16 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 68 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 68 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 68 273
  (Polychromatic418967fa.accept_16_14_4_1_1_3049 14 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 68 273 (accept_3_4 13 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  68 273 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 68 273 (accept_3_4 10 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 68 273 (Polychromatic418967fa.accept_14_9_12_7_1_597 9 68 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 68 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 68 273 (accept_3_4 7 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 68
  273 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 68 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 68 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 68 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 68 273 (accept_3_4 4 68 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 68 273 (Polychromatic418967fa.accept_16_3_4_1_1_2996 3 68 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 68 273 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 68
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 68 273 (accept_3_4 1 68 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 273 (allA_succ_of_accept 66 67
  273 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 273 (accept_3_5 65 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 63 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 273 (accept_3_5 62 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 273 (accept_3_5 59 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 273 (Polychromatic418967fa.accept_15_12_7_3_1_1940 57 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 273 (accept_3_5 56 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 55 67 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 273 (accept_3_5 53 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 273 (accept_3_5 50 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 273 (Polychromatic418967fa.accept_15_4_7_3_1_119 49 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 273
  (Polychromatic418967fa.accept_18_12_13_3_1_6427 48 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 273 (accept_3_5 47 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 273 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 273 (accept_3_5 44 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 273 (accept_3_5 41 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 273 (accept_3_5 38 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 273
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 273 (accept_3_5 35 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 273 (accept_3_5 32 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 273 (Polychromatic418967fa.accept_14_3_11_7_1_1260 31 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 273 (accept_3_5 29 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 273 (accept_3_5 26 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 273 (accept_3_5 23 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 273 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 273 (accept_3_5 20 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 67 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 273 (accept_3_5 17 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 273 (accept_3_5 14 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 273 (Polychromatic418967fa.accept_16_13_3_1_1_2100 13 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 273
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 273 (accept_3_5 11 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 273 (Polychromatic418967fa.accept_18_9_13_3_1_5088 9 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 273 (accept_3_5 8 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 67 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 273 (accept_3_5 5 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 67 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 67 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 67 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 273 (accept_3_5 2 67 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 67 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 67 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 273 (allA_succ_of_accept 65 66
  273 (Polychromatic418967fa.accept_15_5_6_3_1_525 65 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 66 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 64 66 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 66 273 3 21 22 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 66 273
  (Polychromatic418967fa.accept_12_2_6_9_1_19 62 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 66 273 (Polychromatic418967fa.accept_15_1_6_3_1_2827 61 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 273 3 20 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 59
  66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 273
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 66 273 3 19 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 66 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608 56 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 66 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 273 3 18 22 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 273
  (Polychromatic418967fa.accept_14_11_10_7_1_1948 53 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 66 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 52 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 66 273 3 17 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 66 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 50
  66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 66 273
  (Polychromatic418967fa.accept_10_9_6_3_1_545 49 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 273 3 16 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 66 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 66 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 66 273 3 15 22 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 66 273
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 66 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 273 3 14 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 273 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  41 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 273
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 66 273 3 13 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 66 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 66 273 (Polychromatic418967fa.accept_10_7_6_3_1_927 37 66 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 273 3 12 22 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 66 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 66 273 3 11 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 66 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  32 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 66 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 273 3 10 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 273 (Polychromatic418967fa.accept_10_9_6_3_1_545 29 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 66 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 66 273 3 9 22 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 66 273
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 66 273 (Polychromatic418967fa.accept_14_11_10_7_1_1948 25 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 273 3 8 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 66 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 273
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 66 273 3 7 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 66 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 66 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 273 3 6 22 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 273
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 66 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 66 273 3 5 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 66 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 66 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 66 273
  (Polychromatic418967fa.accept_18_13_12_3_1_3857 13 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 273 3 4 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 66 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 66 273 3 3 22 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 66 273
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 66 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 273 3 2 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 273 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 66 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 66 273
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 66 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 66 273 3 1 22 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 66 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 66 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 273 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 66 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 273 (allA_succ_of_accept 64 65 273
  (accept_3_4 64 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 273
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 65 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 273 (accept_3_4 61 65 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 65 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 273 (Polychromatic418967fa.accept_9_5_2_3_1_194 59
  65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 273 (accept_3_4 58 65
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 273
  (Polychromatic418967fa.accept_10_7_5_3_1_542 57 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 65 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 65 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 273 (accept_3_4 55 65 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 65 273 (Polychromatic418967fa.accept_14_12_9_7_1_2762 54 65 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 65 273 13 4 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 65 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 65 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 65 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 65 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 273 (accept_3_4 49 65 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 273 (Polychromatic418967fa.accept_10_8_5_3_1_543
  48 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 273
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 273 (accept_3_4 46 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 273 (Polychromatic418967fa.accept_11_1_10_9_1_871 45 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 65 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 273 (accept_3_4 43 65 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 65 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 273 (accept_3_4 40 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 65
  273 13 3 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38
  65 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 65 273 (accept_3_4 37 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 65 273 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 65 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 273 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 65 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 65 273 (accept_3_4 34 65 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 33
  65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 65 273
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 65 273 (accept_3_4 31 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  65 273 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 65 273 (Polychromatic418967fa.accept_24_5_17_9_1_9969 29 65 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 273 (accept_3_4 28 65 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 65 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 65 273 13 2 5 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 65 273 (accept_3_4 25 65 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 24
  65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 273 (accept_3_4 22 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 273 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 65 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 273 (accept_3_4 19 65 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 273 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 65 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 273 (accept_3_4 16 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 65 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 65 273 13 1 5 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 65 273 (Polychromatic418967fa.accept_10_2_5_3_1_1408
  12 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 273
  (Polychromatic418967fa.accept_19_11_8_7_1_11423 11 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 273 (accept_3_4 10 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 273 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 65 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 273 (accept_3_4 7 65 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 65 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 273 (accept_3_4 4 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  273 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 65 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 65 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 273 (accept_3_4 1 65 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 273
  (allA_succ_of_accept 63 64 273 (Polychromatic418967fa.accept_17_12_13_1_1_4478 63 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 64 273 (accept_3_5 62 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 64 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 60
  64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 273 (accept_3_5 59 64
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 273
  (Polychromatic418967fa.accept_9_4_1_3_1_190 58 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 64 273 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 64 273 (accept_3_5 56 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 64 273 (Polychromatic418967fa.accept_12_6_4_9_1_544
  54 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 273 (accept_3_5 53
  64 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 273
  (Polychromatic418967fa.accept_9_7_1_3_1_443 52 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 64 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 64 273 (accept_3_5 50 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 64 273 (Polychromatic418967fa.accept_14_6_8_7_1_589
  48 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 273 (accept_3_5 47
  64 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 273
  (Polychromatic418967fa.accept_15_1_4_3_1_1928 46 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 64 273 (Polychromatic418967fa.accept_22_1_20_9_1_12053 45 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 64 273 (accept_3_5 44 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 64 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 42
  64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 273 (accept_3_5 41 64
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 273
  (Polychromatic418967fa.accept_9_4_1_3_1_190 40 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 64 273 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 64 273 (accept_3_5 38 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 64 273 (Polychromatic418967fa.accept_17_2_13_1_1_3355
  36 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 273 (accept_3_5 35
  64 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 273
  (Polychromatic418967fa.accept_9_7_1_3_1_443 34 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 64 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 64 273 (accept_3_5 32 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 64 273 (Polychromatic418967fa.accept_12_6_4_9_1_544
  30 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 273 (accept_3_5 29
  64 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 273
  (Polychromatic418967fa.accept_22_6_20_9_1_9031 28 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 64 273 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 64 273 (accept_3_5 26 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 64 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 24
  64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 273 (accept_3_5 23 64
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 273
  (Polychromatic418967fa.accept_9_4_1_3_1_190 22 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 64 273 (Polychromatic418967fa.accept_23_21_18_20_1_2158 21 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 64 273 (accept_3_5 20 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 64 273 (Polychromatic418967fa.accept_12_6_4_9_1_544
  18 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 273 (accept_3_5 17
  64 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 273
  (Polychromatic418967fa.accept_9_7_1_3_1_443 16 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 64 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 64 273 (accept_3_5 14 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 64 273
  (Polychromatic418967fa.accept_17_12_13_1_1_4478 12 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 64 273 (accept_3_5 11 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  64 273 (Polychromatic418967fa.accept_25_10_14_23_1_16725 10 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 64 273 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 64 273 (accept_3_5 8 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 64 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 64 273
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 64 273 (accept_3_5 5 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 64
  273 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 64 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 64 273 (Polychromatic418967fa.accept_20_3_4_13_1_3824 3 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 273 (accept_3_5 2 64 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 64 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 64 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 273 (allA_succ_of_accept 62 63 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 273 3 20 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  59 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 63 273 3 19 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 63 273 7 8 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 63 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 55 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 63 273 3 18 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 63 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 53
  63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 273
  (Polychromatic418967fa.accept_19_14_6_7_1_7223 52 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 63 273 3 17 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 63 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63 273 7 7 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 63 273 3 16 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 63 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 63 273 3 15 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 273 (Polychromatic418967fa.accept_18_8_9_3_1_2645 44 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 273 (Polychromatic418967fa.accept_11_10_8_9_1_492 43 63 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 273 21 2 3 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 273
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 273 (Polychromatic418967fa.accept_16_8_15_1_1_3006 40 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 273 3 13 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 63
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 273
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 273 3 12 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 63 273 7 5 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 63 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 273 3 11 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 273 (Polychromatic418967fa.accept_11_10_8_9_1_492
  32 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 273
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 63 273 3 10 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 63 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 273 7 4 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 63 273 3 9 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 63 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 63 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 273
  (Polychromatic418967fa.accept_12_1_3_9_1_174 25 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 63 273 3 8 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 63 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 273 21 1 3 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 273
  (Polychromatic418967fa.accept_18_2_9_3_1_3825 20 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 63 273 3 6 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 63 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 63 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 273
  (Polychromatic418967fa.accept_17_16_12_1_1_5785 16 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 63 273 3 5 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 63 273 7 2 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 63 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 273 3 4 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 63 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 273 3 3 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 273 (Polychromatic418967fa.accept_16_8_15_1_1_3006 8 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 63 273 7 1 9 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 63 273 3 2 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 63 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 273
  (Polychromatic418967fa.accept_20_4_3_13_1_8257 4 63 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 63 273 3 1 21 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 63 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 63 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 63 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 273 (allA_succ_of_accept 61 62 273
  (accept_3_4 61 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 62 273
  (Polychromatic418967fa.accept_9_6_8_3_1_183 60 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 62 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 62 273 (accept_3_4 58 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 62 273 (Polychromatic418967fa.accept_11_2_7_9_1_890 57 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 62 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 56
  62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 62 273 (accept_3_4 55 62
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 62 273
  (Polychromatic418967fa.accept_12_6_2_9_1_537 54 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 62 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 62 273 (accept_3_4 52 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 62 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 62 273 (Polychromatic418967fa.accept_9_5_8_3_1_437 50
  62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 62 273 (accept_3_4 49 62
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 62 273
  (Polychromatic418967fa.accept_18_12_8_3_1_1627 48 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 62 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 62 273 (accept_3_4 46 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 62 273 (Polychromatic418967fa.accept_10_5_2_3_1_239 45 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 62 273 (Polychromatic418967fa.accept_15_14_2_3_1_1980
  44 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 62 273 (accept_3_4 43
  62 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 62 273
  (Polychromatic418967fa.accept_9_6_8_3_1_183 42 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 62 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 62 273 (accept_3_4 40 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 62 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 62 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 38
  62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 62 273 (accept_3_4 37 62
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 62 273
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 62 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 62 273 (accept_3_4 34 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 62 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 62 273 (Polychromatic418967fa.accept_9_5_8_3_1_437 32
  62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 62 273 (accept_3_4 31 62
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 62 273
  (Polychromatic418967fa.accept_12_6_2_9_1_537 30 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 62 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 62 273 (accept_3_4 28 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 62 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 62 273
  (Polychromatic418967fa.accept_25_1_12_23_1_5960 26 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 62 273 (accept_3_4 25 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  62 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 62 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 62 273 (accept_3_4 22 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 62 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 62 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 62 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 62 273 (accept_3_4 19 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  62 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 62 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 62 273 (accept_3_4 16 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 62 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 62 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 62 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 62 273 (accept_3_4 13 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  62 273 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 62 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 62 273 (accept_3_4 10 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 62 273 (Polychromatic418967fa.accept_18_9_8_3_1_2702 9 62 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 62 273
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 62 273 (accept_3_4 7 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 62
  273 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 62 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 62 273 (accept_3_4 4 62 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 62 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 62 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 62 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  62 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 62 273 (accept_3_4 1 62 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 273 (allA_succ_of_accept 60 61 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 60 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 273 (accept_3_5 59 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 273 (Polychromatic418967fa.accept_16_9_13_1_1_3069 57 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 273 (accept_3_5 56 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 61 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 273
  (Polychromatic418967fa.accept_14_12_5_7_1_2010 54 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 273 (accept_3_5 53 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 273 (accept_3_5 50 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 273
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 273 (accept_3_5 47 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 273 (Polychromatic418967fa.accept_17_11_10_1_1_13244 45 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 273 (accept_3_5 44 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 273 (Polychromatic418967fa.accept_15_13_1_3_1_1972 43 61
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 273 (accept_3_5 41 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 273 (accept_3_5 38 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 273 (accept_3_5 35 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 273 (accept_3_5 32 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 273
  (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 273 (accept_3_5 29 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 273 (accept_3_5 26 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 273 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 273 (accept_3_5 23 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 273 (Polychromatic418967fa.accept_15_6_1_3_1_2852 21 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 273 (accept_3_5 20 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 273
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 273 (accept_3_5 17 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 273 (accept_3_5 14 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 273 (accept_3_5 11 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 273 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 273 (accept_3_5 8 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 273 (Polychromatic418967fa.accept_17_7_10_1_1_4488 7 61 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 273 (accept_3_5 5 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 61 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 273 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 61 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 273 (accept_3_5 2 61 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 61 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 273 (allA_succ_of_accept 59 60 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 60 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 60 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 60 273 3 19 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 60 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 60 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 55 60 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 273 3 18 20 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 273
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 60 273 3 17 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 60 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 50
  60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 60 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 273 3 16 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 60 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 60 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 273 3 15 20 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 60 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 273 3 14 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 60 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 60 273 3 13 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 60 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 60 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 60 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 273 3 12 20 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 60 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 60 273 3 11 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 60 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 60 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 273 3 10 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 60 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 60 273 3 9 20 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 60 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 60 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 273 3 8 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 60 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 60 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 60 273 3 7 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 60 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 60 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 60 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 273 3 6 20 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 60 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 273 3 5 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 60 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 273
  (Polychromatic418967fa.accept_8_5_4_1_1_111 13 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 273 3 4 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 60 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 60 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 60 273 3 3 20 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 60 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 273 3 2 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 60 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 60 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 60 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 60 273 3 1 20 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 60 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 60 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 60 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 60 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 273 (allA_succ_of_accept 58 59 273
  (accept_3_4 58 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 273
  (Polychromatic418967fa.accept_11_2_4_9_1_484 57 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 59 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 273 (accept_3_4 55 59 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 273 (Polychromatic418967fa.accept_9_8_5_3_1_777 53
  59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 59 273 (accept_3_4 52 59
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 59 273
  (Polychromatic418967fa.accept_9_6_5_3_1_205 51 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 59 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 59 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 273 (accept_3_4 49 59 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 59 273 (Polychromatic418967fa.accept_22_4_15_9_1_16724 48 59 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 273 (accept_3_4 46 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 273 (Polychromatic418967fa.accept_17_11_8_1_1_3362 45 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 273 (accept_3_4 43 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 59 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 273
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 41 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 273 (accept_3_4 40 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 273 (accept_3_4 37 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 273 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 59 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 273 (accept_3_4 34 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 273 (accept_3_4 31 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 59 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 273 (accept_3_4 28 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 273 (accept_3_4 25 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 59 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 273
  (Polychromatic418967fa.accept_19_4_2_7_1_4458 23 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 273 (accept_3_4 22 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 273 (Polychromatic418967fa.accept_17_4_8_1_1_5740 21 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 273 (accept_3_4 19 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 59 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 273 (accept_3_4 16 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 273 (accept_3_4 13 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 273 (Polychromatic418967fa.accept_16_12_11_1_1_4088 12 59 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 273 (accept_3_4 10 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 273 (Polychromatic418967fa.accept_17_9_8_1_1_7036 9 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 273 (accept_3_4 7 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 59 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 273
  (Polychromatic418967fa.accept_19_5_2_7_1_1019 5 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 273 (accept_3_4 4 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  273 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 59 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 59 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 273 (accept_3_4 1 59 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 59 273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 273
  (allA_succ_of_accept 57 58 273 (Polychromatic418967fa.accept_15_12_13_3_1_1915 57 58 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 273 (accept_3_5 56 58 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 273 (Polychromatic418967fa.accept_12_6_10_9_1_531
  54 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 273 (accept_3_5 53
  58 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 52 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 273 (accept_3_5 50 58 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 273
  (Polychromatic418967fa.accept_19_10_1_7_1_10040 48 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 273 (accept_3_5 47 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 273 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 273 (accept_3_5 44 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 273 (accept_3_5 41 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 273 (Polychromatic418967fa.accept_14_12_2_7_1_1243 40 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 273 (accept_3_5 38 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 58 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 273
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 273 (accept_3_5 35 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 273 (accept_3_5 32 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 273
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 58 273 (accept_3_5 29 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  58 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 58 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 273 (accept_3_5 26 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 58 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 273 (accept_3_5 23 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 273 (Polychromatic418967fa.accept_20_2_18_13_1_3843 22 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 273 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 273 (accept_3_5 20 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 273
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 273 (accept_3_5 17 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 273 (accept_3_5 14 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 58 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 273
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 273 (accept_3_5 11 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 273 (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 273 (accept_3_5 8 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 273 (accept_3_5 5 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  273 (Polychromatic418967fa.accept_19_4_1_7_1_4438 4 58 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 58 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 273 (accept_3_5 2 58 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 58 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 58 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 273 (allA_succ_of_accept 56 57 273
  (Polychromatic418967fa.accept_10_6_7_3_1_547 56 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 273 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 273 3 18 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 273 (Polychromatic418967fa.accept_15_8_12_3_1_1912
  53 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 273
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 52 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 57 273 3 17 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 57 273 (Polychromatic418967fa.accept_14_8_1_7_1_3725 50 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 273 (Polychromatic418967fa.accept_25_24_7_23_1_16723 49 57
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 57 273 3 16 19 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 57 273
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 47 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 57 273 (Polychromatic418967fa.accept_10_6_7_3_1_547 46 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 273 3 15 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 273 (Polychromatic418967fa.accept_10_4_7_3_1_54 44
  57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 273
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 43 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 57 273 3 14 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 57 273 (Polychromatic418967fa.accept_14_13_1_7_1_1211 41 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 273 (Polychromatic418967fa.accept_11_7_2_9_1_480 40 57 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 57 273 3 13 19 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 57 273
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 38 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 273 (Polychromatic418967fa.accept_11_4_2_9_1_496 37 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 273 3 12 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 273 (Polychromatic418967fa.accept_10_5_7_3_1_561 35
  57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 273
  (Polychromatic418967fa.accept_10_4_7_3_1_54 34 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 57 273 3 11 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 57 273 (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 273 (Polychromatic418967fa.accept_23_8_11_20_1_16722 31 57
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 57 273 3 10 19 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 57 273
  (Polychromatic418967fa.accept_11_7_2_9_1_480 29 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 57 273 (Polychromatic418967fa.accept_15_13_12_3_1_1180 28 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 273 3 9 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 273 (Polychromatic418967fa.accept_10_6_7_3_1_547 26 57 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 273
  (Polychromatic418967fa.accept_10_5_7_3_1_561 25 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 57 273 3 8 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 57 273 (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 273 (Polychromatic418967fa.accept_14_8_1_7_1_3725 22 57 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 57 273 3 7 19 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 57 273
  (Polychromatic418967fa.accept_14_6_1_7_1_2775 20 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 273 (Polychromatic418967fa.accept_17_2_6_1_1_8357 19 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 273 3 6 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 273 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 57 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 273
  (Polychromatic418967fa.accept_10_6_7_3_1_547 16 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 57 273 3 5 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 57 273 (Polychromatic418967fa.accept_10_4_7_3_1_54 14 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 273 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 57
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 57 273 3 4 19 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 57 273
  (Polychromatic418967fa.accept_22_11_13_9_1_16721 11 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 57 273 (Polychromatic418967fa.accept_16_10_9_1_1_9973 10 57 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 273 3 3 19 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 273
  (Polychromatic418967fa.accept_14_8_1_7_1_3725 8 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 273 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 273 3 2 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 273 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 57 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 273
  (Polychromatic418967fa.accept_10_4_7_3_1_54 4 57 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 57 273 3 1 19 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 57 273 (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 57 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 273 (Polychromatic418967fa.accept_22_1_13_9_1_16720 1 57 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 273 (allA_succ_of_accept 55 56 273
  (accept_3_4 55 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 56 273
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 56 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 56 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 56 273 (accept_3_4 52 56 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 56 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 56 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 56 273 (Polychromatic418967fa.accept_9_5_2_3_1_194 50
  56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 56 273 7 7 8 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 56 273
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 56 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 56 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 56 273 (accept_3_4 46 56 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 56 273 (Polychromatic418967fa.accept_18_9_2_3_1_5082 45 56 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 56 273 (Polychromatic418967fa.accept_9_8_2_3_1_447 44
  56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 56 273 (accept_3_4 43 56
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 273 7 6 8 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 273
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 56 273 (accept_3_4 40 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  56 273 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 56 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 56 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 56 273 (accept_3_4 37 56 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 56 273 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 56 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 56 273 7 5 8 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 56 273 (accept_3_4 34 56 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 56 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 56 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 56 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 56 273 (accept_3_4 31 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  56 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 56 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 56 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 273 7 4 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 273 (Polychromatic418967fa.accept_10_7_6_3_1_927 27
  56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 56 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 56 273 (accept_3_4 25 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  56 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 56 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 56 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 56 273 (accept_3_4 22 56 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 56 273 7 3 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 56 273 (Polychromatic418967fa.accept_16_4_8_1_1_5257 20 56 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 56 273 (accept_3_4 19 56 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 56 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 56 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 56 273
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 56 273 (accept_3_4 16 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  56 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 56 273 7 2 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 56 273 (accept_3_4 13 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 56 273 (Polychromatic418967fa.accept_16_12_8_1_1_5270 12 56 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 56 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 56 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 56 273 (accept_3_4 10 56 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 56 273 (Polychromatic418967fa.accept_10_9_6_3_1_545 9
  56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 56 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 56 273 7 1 8 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 56 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 56 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 56 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 56 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 56 273 (accept_3_4 4 56 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 56 273 (Polychromatic418967fa.accept_20_3_16_13_1_8307
  3 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 56 273
  (Polychromatic418967fa.accept_29_2_27_12_1_16719 2 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 56 273 (accept_3_4 1 56 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  273)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 273 (allA_succ_of_accept 54 55 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 273 (accept_3_5 53 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 273 (accept_3_5 50 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 55 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 273
  (Polychromatic418967fa.accept_10_8_5_3_1_543 48 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 273 (accept_3_5 47 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 273 (Polychromatic418967fa.accept_18_9_1_3_1_6451 45 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 273 (accept_3_5 44 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 55 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 273 (accept_3_5 41 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 273 (accept_3_5 38 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 55 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 273
  (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 273 (accept_3_5 35 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 273 (accept_3_5 32 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 55 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 273 (accept_3_5 29 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 273 (accept_3_5 26 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 55 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 273
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 273 (accept_3_5 23 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 273 (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 55 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 273 (accept_3_5 20 55 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 273 (Polychromatic418967fa.accept_22_19_11_9_1_9028 19 55
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 273 (accept_3_5 17 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 273 (accept_3_5 14 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 55 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 273
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 273 (accept_3_5 11 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 273 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 273 (accept_3_5 8 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 55 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 273 (accept_3_5 5 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 55 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 55 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 273 (accept_3_5 2 55 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 273 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 55 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 273)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 273 (allA_succ_of_accept 53 54 273 (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 54 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 54 273
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 52 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 54 273 3 17 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 54 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 273 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 54 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 273 3 16 18 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 54 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 54 273 3 15 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 54 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  44 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 273 3 14 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 273 (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 54 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 54 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 54 273 3 13 18 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 54 273
  (Polychromatic418967fa.accept_12_2_6_9_1_19 38 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 54 273 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 273 3 12 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 54 273
  (Polychromatic418967fa.accept_11_1_10_9_1_871 34 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 54 273 3 11 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 54 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 273 3 10 18 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 273
  (Polychromatic418967fa.accept_10_9_4_3_1_539 29 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 54 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 54 273 3 9 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 54 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 54 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 273
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 273 3 8 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 54 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 54 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 54 273 3 7 18 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 54 273
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 54 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 273 3 6 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 273 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 54 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 54 273
  (Polychromatic418967fa.accept_12_4_6_9_1_548 16 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 54 273 3 5 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 54 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 273 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 54
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 273 3 4 18 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 54 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 54 273 3 3 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 54 273 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 54 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 273 3 2 18 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 273 (Polychromatic418967fa.accept_14_5_12_7_1_2767 5 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 54 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 54 273 3 1 18 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 54 273
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 54 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 54 273 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 54 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 54 273)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53
  273 (allA_succ_of_accept 52 53 273 (accept_3_4 52 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 53 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 273 (accept_3_4 49 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 273 (Polychromatic418967fa.accept_23_2_7_20_1_16718 48 53 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 47 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 273 (accept_3_4 46 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 273 (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 273 (accept_3_4 43 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 53 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 273 (accept_3_4 40 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 273 (accept_3_4 37 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 53 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 273
  (Polychromatic418967fa.accept_15_5_8_3_1_556 35 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 273 (accept_3_4 34 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 273 (accept_3_4 31 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 273 (Polychromatic418967fa.accept_17_13_2_1_1_4483 30 53 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 273 (accept_3_4 28 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 273 (accept_3_4 25 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 53 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 273 (accept_3_4 22 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 273 (Polychromatic418967fa.accept_29_21_24_12_1_16717 21 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 273 (accept_3_4 19 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 273 (Polychromatic418967fa.accept_14_4_11_7_1_1234 18 53 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 273
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 17 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 273 (accept_3_4 16 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 273 (accept_3_4 13 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 53 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 273 (accept_3_4 10 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 273 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 273 (accept_3_4 7 53 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 53 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 273 (accept_3_4 4 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  273 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 53 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 53 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 273 (accept_3_4 1 53 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 273))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 273
  (allA_succ_of_accept 51 52 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 52 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 273 (accept_3_5 50 52 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 52 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 52 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 273
  (Polychromatic418967fa.accept_19_10_14_7_1_11440 48 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 52 273 (accept_3_5 47 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 52 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 52 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 52 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 52 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 273 (accept_3_5 44 52 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 43
  52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 273 (accept_3_5 41 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 52 273 13 3 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 52 273 (accept_3_5 38 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 52 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 52 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 273 (Polychromatic418967fa.accept_23_13_6_20_1_10436 36 52
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 52 273 (accept_3_5 35 52 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 52 273 (Polychromatic418967fa.accept_15_4_7_3_1_119
  34 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 52 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 52 273 (accept_3_5 32 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  52 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 52 273 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 52 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 52 273 (accept_3_5 29 52 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 52 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 52 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 52 273
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 273 13 2 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 52 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 52 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 52 273 (accept_3_5 23 52 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 52 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 22
  52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 52 273
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 52 273 (accept_3_5 20 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  52 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 52 273 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 52 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 52 273 (accept_3_5 17 52 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 52 273 (Polychromatic418967fa.accept_22_16_8_9_1_12072 16 52 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 52 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 52 273 (accept_3_5 14 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 52
  273 13 1 4 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12
  52 273 (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 52 273 (accept_3_5 11 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 52 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 52 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 52 273 (Polychromatic418967fa.accept_23_9_6_20_1_5202 9 52 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 273 (accept_3_5 8 52 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 52
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 273 (accept_3_5 5 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  273 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 52 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 273 (Polychromatic418967fa.accept_14_3_10_7_1_3773 3 52 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 273 (accept_3_5 2 52 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 52 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 273))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 273 (allA_succ_of_accept 50 51 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 51 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 51 273 3 16 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 51 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 51 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 51 273 3 15 17 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 51 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 273 3 14 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 51 273 3 13 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 51 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 51 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 51 273 3 12 17 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 51 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 273 3 11 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 51 273 3 10 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 51 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 51 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 51 273 3 9 17 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 51 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 273 3 8 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 51 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 51 273 3 7 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 51 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 51 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 51 273 3 6 17 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 51 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 273 3 5 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 51 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 51 273 3 4 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 51 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 51 273 3 3 17 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 51 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 273 3 2 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 51 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 51 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 51 273 3 1 17 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 51 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 51 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 51 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  273))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 273 (allA_succ_of_accept 49 50 273 (accept_3_4 49
  50 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 50 273
  (Polychromatic418967fa.accept_14_6_8_7_1_589 48 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 50 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 50 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 50 273 (accept_3_4 46 50 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 50 273 (Polychromatic418967fa.accept_18_9_14_3_1_6407 45 50 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 50 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 44 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 50 273 (accept_3_4 43 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  50 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 50 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 50 273 (accept_3_4 40 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 50 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 50 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 50 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 50 273 (accept_3_4 37 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  50 273 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 50 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 50 273 (accept_3_4 34 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 50 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 50 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 50 273
  (Polychromatic418967fa.accept_15_2_5_3_1_552 32 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 50 273 (accept_3_4 31 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  50 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 50 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 50 273 (accept_3_4 28 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 50 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 50 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 50 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 50 273 (accept_3_4 25 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  50 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 50 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 50 273 (accept_3_4 22 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 50 273 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 50 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 50 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 50 273 (accept_3_4 19 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  50 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 50 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 50 273 (accept_3_4 16 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 50 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 50 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 50 273
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 50 273 (accept_3_4 13 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  50 273 (Polychromatic418967fa.accept_16_12_2_1_1_1215 12 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 50 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 50 273 (accept_3_4 10 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 50 273 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 50 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 50 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 50 273 (accept_3_4 7 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 50
  273 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 50 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 50 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 50 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 50 273 (accept_3_4 4 50 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 50 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 50 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 50 273 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 50
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 50 273 (accept_3_4 1 50 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50 273)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  49 273 (allA_succ_of_accept 48 49 273 (Polychromatic418967fa.accept_18_12_13_3_1_6427 48 49 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 273 (accept_3_5 47 49 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 49 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 273
  (Polychromatic418967fa.accept_18_9_13_3_1_5088 45 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 273 (accept_3_5 44 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 49 273 7 6 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 49 273 (accept_3_5 41 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 49 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 49 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 49 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 273 (accept_3_5 38 49 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 37
  49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 273
  (Polychromatic418967fa.accept_10_6_9_3_1_935 36 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 49 273 7 5 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 49 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 49 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 49 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 273 (accept_3_5 32 49 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 273 (Polychromatic418967fa.accept_15_1_4_3_1_1928
  31 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 273
  (Polychromatic418967fa.accept_18_12_13_3_1_6427 30 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 273 (accept_3_5 29 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 49
  273 7 4 7 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  49 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 49 273 (accept_3_5 26 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 49 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 49 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 49 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 273 (accept_3_5 23 49 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 22
  49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 49 273 7 3 7 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 49 273 (accept_3_5 20
  49 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 49 273 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 49 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 273 (accept_3_5 17 49 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 49 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 49 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 49 273 7 2 7 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 49 273
  (Polychromatic418967fa.accept_19_13_11_7_1_4451 13 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 49 273 (Polychromatic418967fa.accept_17_12_15_1_1_5798 12 49 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 273 (accept_3_5 11 49 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 49 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 49 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 273 (Polychromatic418967fa.accept_17_9_15_1_1_7048
  9 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 273 (accept_3_5 8 49
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 49 273 7 1 7 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 49 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 273 (accept_3_5 5 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 49 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 49 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 273 (accept_3_5 2 49 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 49 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 273))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 273 (allA_succ_of_accept 47 48 273 (Polychromatic418967fa.accept_17_13_14_1_1_2258 47 48 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 273 (Polychromatic418967fa.accept_10_6_8_3_1_930
  46 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 48 273 3 15 16 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 48 273
  (Polychromatic418967fa.accept_17_10_14_1_1_5823 44 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 48 273 (Polychromatic418967fa.accept_14_1_6_7_1_1936 43 48 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 273 3 14 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 273 (Polychromatic418967fa.accept_10_1_8_3_1_947 41
  48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 273
  (Polychromatic418967fa.accept_23_17_2_20_1_13543 40 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 48 273 3 13 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 48 273 (Polychromatic418967fa.accept_17_4_14_1_1_1363 38 48 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 48 273
  (Polychromatic418967fa.accept_18_1_12_3_1_6426 37 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 273 3 12 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 273 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 48 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 273 (Polychromatic418967fa.accept_20_14_8_13_1_8293 34 48
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 48 273 3 11 16 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 48 273
  (Polychromatic418967fa.accept_18_14_12_3_1_5103 32 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 48 273 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 48 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 273 3 10 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 273 (Polychromatic418967fa.accept_14_1_6_7_1_1936
  29 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 48 273
  (Polychromatic418967fa.accept_19_9_10_7_1_10002 28 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 48 273 3 9 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 48 273 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 48 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 273 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 48 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 273 3 8 16 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 273
  (Polychromatic418967fa.accept_20_3_8_13_1_3832 23 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 48 273 (Polychromatic418967fa.accept_14_8_6_7_1_1934 22 48 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 48 273 3 7 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 48 273 (Polychromatic418967fa.accept_18_2_12_3_1_2707 20 48 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 273
  (Polychromatic418967fa.accept_18_1_12_3_1_6426 19 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 273 3 6 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 273 (Polychromatic418967fa.accept_19_17_10_7_1_11430 17 48 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 48 273 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 48 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 48 273 3 5 16 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 48 273
  (Polychromatic418967fa.accept_18_14_12_3_1_5103 14 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 48 273 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 48 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 273 3 4 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 273 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 48 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 48 273
  (Polychromatic418967fa.accept_17_10_14_1_1_5823 10 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 48 273 3 3 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 48 273 (Polychromatic418967fa.accept_14_8_6_7_1_1934 8 48 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 273 (Polychromatic418967fa.accept_18_7_12_3_1_804 7 48 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 273 3 2 16 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48 273
  (Polychromatic418967fa.accept_10_5_8_3_1_229 5 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 48 273 (Polychromatic418967fa.accept_17_4_14_1_1_1363 4 48 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 48 273 3 1 16 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 48 273 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 48 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 48 273
  (Polychromatic418967fa.accept_10_1_8_3_1_947 1 48 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 48 273)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 273 (allA_succ_of_accept 46 47 273
  (accept_3_4 46 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 273
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 273 (accept_3_4 43 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 47 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 273 (Polychromatic418967fa.accept_9_5_2_3_1_194 41
  47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 273 (accept_3_4 40 47
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 273
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 273 (accept_3_4 37 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 273 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 47 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 273 (Polychromatic418967fa.accept_9_8_2_3_1_447 35
  47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 273 (accept_3_4 34 47
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 273
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 273 (accept_3_4 31 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 47 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 273 (Polychromatic418967fa.accept_15_14_2_3_1_1980
  29 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 273 (accept_3_4 28
  47 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 273
  (Polychromatic418967fa.accept_12_3_11_9_1_193 27 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 273 (accept_3_4 25 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 47 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 273 (Polychromatic418967fa.accept_9_5_2_3_1_194 23
  47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 273 (accept_3_4 22 47
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 273
  (Polychromatic418967fa.accept_16_5_15_1_1_2113 21 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 273 (accept_3_4 19 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 47 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 273 (Polychromatic418967fa.accept_9_8_2_3_1_447 17
  47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 273 (accept_3_4 16 47
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 273
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 47 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 273 (accept_3_4 13 47 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 47 273 (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 47 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 273
  (Polychromatic418967fa.accept_16_11_15_1_1_2074 11 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 273 (accept_3_4 10 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 273 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 47 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 273 (accept_3_4 7 47 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 47 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 273 (accept_3_4 4 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  273 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 47 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 47 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 47 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 273 (accept_3_4 1 47 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 47 273))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 273
  (allA_succ_of_accept 45 46 273 (Polychromatic418967fa.accept_14_3_4_7_1_175 45 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 46 273 (accept_3_5 44 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 46 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 46 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 42
  46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 273 (accept_3_5 41 46
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 273
  (Polychromatic418967fa.accept_9_4_1_3_1_190 40 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 46 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 46 273 (accept_3_5 38 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 46 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 46 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 46 273 (Polychromatic418967fa.accept_15_6_1_3_1_2852
  36 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 273 (accept_3_5 35
  46 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 273
  (Polychromatic418967fa.accept_9_7_1_3_1_443 34 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 46 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 46 273 (accept_3_5 32 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 46 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 46 273 (Polychromatic418967fa.accept_12_6_10_9_1_531
  30 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 273 (accept_3_5 29
  46 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 273
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 46 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 46 273 (accept_3_5 26 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 46 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 46 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 46 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 24
  46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 273 (accept_3_5 23 46
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 273
  (Polychromatic418967fa.accept_9_4_1_3_1_190 22 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 46 273 (Polychromatic418967fa.accept_15_6_1_3_1_2852 21 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 46 273 (accept_3_5 20 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 46 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 46 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  18 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 273 (accept_3_5 17
  46 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 273
  (Polychromatic418967fa.accept_9_7_1_3_1_443 16 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 46 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 46 273 (accept_3_5 14 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 46 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 46 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 46 273 (Polychromatic418967fa.accept_19_12_8_7_1_7209
  12 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 273 (accept_3_5 11
  46 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 273
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 46 273 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 46 273 (accept_3_5 8 46 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 46 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 46 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 273 (accept_3_5 5 46 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 46 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 4
  46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 46 273 (accept_3_5 2 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46
  273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 46 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 46 273)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 273 (allA_succ_of_accept 44 45 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 273 (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 45 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 273 3 14 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 273 (Polychromatic418967fa.accept_16_9_13_1_1_3069
  41 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 273
  (Polychromatic418967fa.accept_23_17_22_20_1_16716 40 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 45 273 3 13 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 45 273 (Polychromatic418967fa.accept_10_8_5_3_1_543 38 45 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 273
  (Polychromatic418967fa.accept_10_7_5_3_1_542 37 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 45 273 3 12 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 45 273 (Polychromatic418967fa.accept_16_3_13_1_1_1206 35 45 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 273 (Polychromatic418967fa.accept_22_12_1_9_1_16715 34 45
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 273 3 11 15 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 273
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 273 (Polychromatic418967fa.accept_18_13_9_3_1_5114 31 45 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 273 3 10 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 273
  (Polychromatic418967fa.accept_25_4_20_23_1_16714 29 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 45 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 45 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 273 3 9 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 273 (Polychromatic418967fa.accept_18_8_9_3_1_2645
  26 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 273
  (Polychromatic418967fa.accept_14_11_3_7_1_604 25 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 45 273 3 8 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 45 273 (Polychromatic418967fa.accept_27_23_18_3_1_16713 23 45 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 273 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 45 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 45 273 3 7 15 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 45 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 20 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 273 (Polychromatic418967fa.accept_16_3_13_1_1_1206 19 45 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 273 3 6 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 45 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 273
  (Polychromatic418967fa.accept_25_16_20_23_1_16712 16 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 45 273 3 5 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 45 273 (Polychromatic418967fa.accept_16_14_13_1_1_5278 14 45 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 273
  (Polychromatic418967fa.accept_18_13_9_3_1_5114 13 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 273 3 4 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 273 (Polychromatic418967fa.accept_14_11_3_7_1_604 11 45 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 273 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 45
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 273 3 3 15 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 273
  (Polychromatic418967fa.accept_10_8_5_3_1_543 8 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 45 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 273 3 2 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 273 (Polychromatic418967fa.accept_16_5_13_1_1_2084 5 45 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 273
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 45 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 273 3 1 15 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 273 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 45 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 273 (Polychromatic418967fa.accept_18_1_9_3_1_2672 1 45 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  273))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 273 (allA_succ_of_accept 43 44 273 (accept_3_4 43 44
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 44 273
  (Polychromatic418967fa.accept_9_6_8_3_1_183 42 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 44 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 44 273 (accept_3_4 40 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 44 273 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 44 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 44 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 38
  44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 44 273 (accept_3_4 37 44
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 44 273
  (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 44 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 44 273 (accept_3_4 34 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 44 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 44 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 44 273 (Polychromatic418967fa.accept_9_5_8_3_1_437 32
  44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 44 273 (accept_3_4 31 44
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 44 273
  (Polychromatic418967fa.accept_12_6_8_9_1_553 30 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 44 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 44 273 (accept_3_4 28 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 44 273 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 44 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 44 273 (Polychromatic418967fa.accept_14_12_2_7_1_1243
  26 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 44 273 (accept_3_4 25
  44 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 44 273
  (Polychromatic418967fa.accept_9_6_8_3_1_183 24 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 44 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 44 273 (accept_3_4 22 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 44 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 44 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 44 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 20
  44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 44 273 (accept_3_4 19 44
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 44 273
  (Polychromatic418967fa.accept_12_6_8_9_1_553 18 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 44 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 44 273 (accept_3_4 16 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 44 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 44 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 44 273 (Polychromatic418967fa.accept_9_5_8_3_1_437 14
  44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 44 273 (accept_3_4 13 44
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 44 273
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 44 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 44 273 (accept_3_4 10 44 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 44 273 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 44 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 44 273 (Polychromatic418967fa.accept_16_8_12_1_1_7720
  8 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 44 273 (accept_3_4 7 44
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 44 273 (Polychromatic418967fa.accept_9_6_8_3_1_183
  6 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 44 273
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 44 273 (accept_3_4 4 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 44
  273 (Polychromatic418967fa.accept_19_3_6_7_1_10044 3 44 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 44 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 44 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 44 273 (accept_3_4 1 44 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 44 273)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 273
  (allA_succ_of_accept 42 43 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 273 (accept_3_5 41 43 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 43 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  39 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 273 (accept_3_5 38
  43 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 273
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 43 273 (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 43 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 273 (accept_3_5 35 43 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 43 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 33
  43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 273 (accept_3_5 32 43
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 273 (Polychromatic418967fa.accept_9_4_7_3_1_43
  31 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 273 (accept_3_5 29 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 43 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 273 (accept_3_5 26 43 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 273 (Polychromatic418967fa.accept_15_10_13_3_1_4816 25 43 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 273 (accept_3_5 23 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 273 (Polychromatic418967fa.accept_19_2_5_7_1_10021 21 43 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 273 (accept_3_5 20 43 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 43 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 273 (accept_3_5 17 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 43 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 273 (accept_3_5 14 43 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 43 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 273
  (Polychromatic418967fa.accept_11_1_10_9_1_871 12 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 273 (accept_3_5 11 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 273 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 43 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 273 (accept_3_5 8 43 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 273 (Polychromatic418967fa.accept_25_7_18_23_1_16711 7 43 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 273 (accept_3_5 5 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 43 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 43 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 273 (accept_3_5 2 43 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 43 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 273))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 273
  (allA_succ_of_accept 41 42 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 42 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 42 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 42 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 42 273 3 13 14 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 42 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 42 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 42 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 42 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 273 3 12 14 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 273 7 5 6 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 42 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 34
  42 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 42 273 3 11 14 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 42 273
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 42 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 42 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 273 3 10 14 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  42 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 273 7 4 6 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 42 273 3 9 14 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 42 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 42 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 42 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 42 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 273 3 8 14 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 42 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 42 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 42 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 42 273 21 1 2 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 42 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 42 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 273 3 6 14 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 42 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 42 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 42 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 42 273 3 5 14 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 273 7 2 6 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 42 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 273 3 4 14 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 42 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 42 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 42 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 42 273 3 3 14 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 42 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 42 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 42 273 7 1 6 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 273 3 2 14 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 273
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 42 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 42 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 42 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 42 273 3 1 14 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 42 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 42 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 42 273
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 42 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 273)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 273 (allA_succ_of_accept 40 41 273
  (accept_3_4 40 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 273
  (Polychromatic418967fa.accept_12_3_5_9_1_176 39 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 41 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 273 (accept_3_4 37 41 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 273 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 41 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 273 (accept_3_4 34 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 41 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 273 (accept_3_4 31 41 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 273 (Polychromatic418967fa.accept_20_10_1_13_1_3848 30 41 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 273 (accept_3_4 28 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 41 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 273 (accept_3_4 25 41 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 41 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 273
  (Polychromatic418967fa.accept_15_8_11_3_1_3847 23 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 273 (accept_3_4 22 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 273 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 41 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 273 (accept_3_4 19 41 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 273 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 41 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 273 (accept_3_4 16 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 41 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 273 (accept_3_4 13 41 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 273 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 41 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 273 (accept_3_4 10 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 273 (Polychromatic418967fa.accept_27_9_14_3_1_16710 9 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 41 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 273 (accept_3_4 7 41 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 41 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 273
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 5 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 273 (accept_3_4 4 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  273 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 41 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 41 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 273 (accept_3_4 1 41 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 273))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 273 (allA_succ_of_accept 39 40 273
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 39 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 273 (accept_3_5 38 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 273 (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 40 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 40 273 (accept_3_5 35 40 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 40 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 40 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 273 (accept_3_5 32 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 40 273 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 40 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 40 273 (accept_3_5 29 40 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 40 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 40 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 273
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 40 273 (accept_3_5 26 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  40 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 40 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 40 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 273 (accept_3_5 23 40 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 273 (Polychromatic418967fa.accept_15_7_10_3_1_2891 22 40 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 40 273
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 40 273 (accept_3_5 20 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  40 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 40 273 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 40 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 40 273 (accept_3_5 17 40 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 40 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 40 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 40 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 40 273 (accept_3_5 14 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  40 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 40 273 (Polychromatic418967fa.accept_16_12_8_1_1_5270 12 40 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 40 273 (accept_3_5 11 40 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 40 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 40 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 40 273
  (Polychromatic418967fa.accept_14_9_12_7_1_597 9 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 273 (accept_3_5 8 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  273 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 40 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 40 273 (accept_3_5 5 40 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 40 273 (Polychromatic418967fa.accept_16_4_8_1_1_5257 4 40 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 273 (Polychromatic418967fa.accept_17_3_6_1_1_8382 3
  40 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 40 273 (accept_3_5 2 40 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 40
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  273)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 273 (allA_succ_of_accept 38 39 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 39 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 37 39 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 273 3 12 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  35 39 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 39 273 3 11 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 39 273 (Polychromatic418967fa.accept_14_4_11_7_1_1234 32 39 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 39 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 39 273 3 10 13 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 39 273
  (Polychromatic418967fa.accept_12_5_3_9_1_541 29 39 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 39 273 (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 39 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 273 3 9 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 39 273 13 2 3 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 39 273 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 39 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 273 3 8 13 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 273
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 39 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 39 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 39 273 3 7 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 39 273 (Polychromatic418967fa.accept_15_5_9_3_1_528 20 39 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 273
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 39 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 39 273 3 6 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 39 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 39 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 273 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 39 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 273 3 5 13 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 39 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 39 273 13 1 3 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 39 273 3 4 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 39 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 39 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 273 3 3 13 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 273
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 39 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 39 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 273 3 2 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 273 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 39 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 273
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 39 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 39 273 3 1 13 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 39 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 39 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 39 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 273)))))))))))))))))))))))))))))))))))))))
  (allB_succ 38 273 (allA_succ_of_accept 37 38 273 (accept_3_4 37 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 38 273 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 38 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 38 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 38 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 38 273 (accept_3_4 34 38 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 38 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 33
  38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 38 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 38 273 (accept_3_4 31 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  38 273 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 38 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 38 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 38 273 (accept_3_4 28 38 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 38 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 38 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 38 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 38 273 (accept_3_4 25 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  38 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 38 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 38 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 38 273 (accept_3_4 22 38 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 38 273 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 38 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 38 273
  (Polychromatic418967fa.accept_15_5_8_3_1_556 20 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 38 273 (accept_3_4 19 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  38 273 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 38 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 38 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 38 273 (accept_3_4 16 38 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 38 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 38 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 38 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 38 273 (accept_3_4 13 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  38 273 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 38 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 38 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 38 273 (accept_3_4 10 38 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 38 273 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 38 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 38 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 38 273 (accept_3_4 7 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 38
  273 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 38 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 38 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 38 273 (accept_3_4 4 38 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 38 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 38 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 38 273 (Polychromatic418967fa.accept_16_2_6_1_1_2069 2
  38 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 38 273 (accept_3_4 1 38 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 38 273)))))))))))))))))))))))))))))))))))))) (allB_succ 37 273
  (allA_succ_of_accept 36 37 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 37 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 37 273 (accept_3_5 35 37 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 37 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 37 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 33
  37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 273 (accept_3_5 32 37
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 273
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 37 273 (Polychromatic418967fa.accept_14_2_9_7_1_5633 30 37 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 37 273 (accept_3_5 29 37 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 37 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 37 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 37 273 (Polychromatic418967fa.accept_12_3_1_9_1_202
  27 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 273 (accept_3_5 26
  37 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 273
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 37 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 37 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 37 273 (accept_3_5 23 37 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 37 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 37 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 37 273
  (Polychromatic418967fa.accept_26_21_11_13_1_16709 21 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 37 273 (accept_3_5 20 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 37 273 (Polychromatic418967fa.accept_14_5_9_7_1_590 19 37 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 273 (Polychromatic418967fa.accept_22_18_15_9_1_16708 18 37
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 37 273 (accept_3_5 17 37 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 37 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16
  37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 273
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 37 273 (accept_3_5 14 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  37 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 37 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 37 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 37 273 (accept_3_5 11 37 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 37 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 37 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 37 273
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 37 273 (accept_3_5 8 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 37
  273 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 37 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 37 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 37 273 (accept_3_5 5 37 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 37 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 37 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 37 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 3
  37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 273 (accept_3_5 2 37 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 273 (Polychromatic418967fa.accept_19_1_18_7_1_12744
  1 37 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37
  273))))))))))))))))))))))))))))))))))))) (allB_succ 36 273 (allA_succ_of_accept 35 36 273
  (Polychromatic418967fa.accept_15_5_6_3_1_525 35 36 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 36 273 (Polychromatic418967fa.accept_14_6_8_7_1_589 34 36 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 36 273 3 11 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 36 273
  (Polychromatic418967fa.accept_19_13_17_7_1_12726 32 36 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 36 273 (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 36 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 273 3 10 12 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 273
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 36 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 36 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 36 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 36 273 3 9 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 36 273 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 36 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 273
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 36 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 36 273 3 8 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 36 273 (Polychromatic418967fa.accept_17_6_2_1_1_3350 23 36 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 36 273 (Polychromatic418967fa.accept_25_22_11_23_1_11541 22 36
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 36 273 3 7 12 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 36 273
  (Polychromatic418967fa.accept_14_6_8_7_1_589 20 36 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 36 273 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 36 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 273 3 6 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 273 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 36 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 36 273
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 36 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 36 273 3 5 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 36 273 (Polychromatic418967fa.accept_16_14_4_1_1_3049 14 36 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 36 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 273 3 4 12 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 273
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 36 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 36 273 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 36 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 36 273 3 3 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 36 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 36 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 273
  (Polychromatic418967fa.accept_10_7_6_3_1_927 7 36 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 273 3 2 12 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 36 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36 273 (Polychromatic418967fa.accept_23_4_13_20_1_16707 4 36
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 36 273 3 1 12 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 36 273
  (Polychromatic418967fa.accept_19_2_17_7_1_8735 2 36 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 36 273 (Polychromatic418967fa.accept_14_1_8_7_1_1253 1 36 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 273)))))))))))))))))))))))))))))))))))) (allB_succ 35 273
  (allA_succ_of_accept 34 35 273 (accept_3_4 34 35 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 35 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 35 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 273 (accept_3_4 31 35 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 35 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 35 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 35 273 7 4 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 35 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 35 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 35 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 273 (accept_3_4 25 35 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 24
  35 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 35 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 273 (accept_3_4 22 35 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 35
  273 7 3 5 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  35 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 35 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 35 273 (accept_3_4 19 35 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 35 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 35 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 35 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 273 (accept_3_4 16 35 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 15
  35 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 35 273 7 2 5 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 273 (accept_3_4 13
  35 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 273
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 35 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 35 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 35 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 273 (accept_3_4 10 35 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 35 273 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 35 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 35
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 273 7 1 5 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 35 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 273 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 35 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 273 (accept_3_4 4 35 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 273 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 35 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 35
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 273 (accept_3_4 1 35 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 273))))))))))))))))))))))))))))))))))) (allB_succ 34 273
  (allA_succ_of_accept 33 34 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 34 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 34 273 (accept_3_5 32 34 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 34 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 34 273 (Polychromatic418967fa.accept_12_6_10_9_1_531
  30 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 273 (accept_3_5 29
  34 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 273
  (Polychromatic418967fa.accept_9_1_7_3_1_41 28 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 34 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 34 273 (accept_3_5 26 34 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 34 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 34 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 34 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 24
  34 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 273 (accept_3_5 23 34
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 273 (Polychromatic418967fa.accept_9_4_7_3_1_43
  22 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 273
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 273 (accept_3_5 20 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 273 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 34 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 273 (accept_3_5 17 34 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 273 (Polychromatic418967fa.accept_15_1_4_3_1_1928 16 34 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 273 (accept_3_5 14 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 273 (Polychromatic418967fa.accept_16_12_2_1_1_1215 12 34 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 273 (accept_3_5 11 34 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 34 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 273
  (Polychromatic418967fa.accept_10_9_4_3_1_539 9 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 273 (accept_3_5 8 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 34 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 273 (accept_3_5 5 34 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 34 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 273 (accept_3_5 2 34 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 34
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 273))))))))))))))))))))))))))))))))))
  (allB_succ 33 273 (allA_succ_of_accept 32 33 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 33 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 33 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 33 273 3 10 11 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 33 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 33 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 33 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 33 273 3 9 11 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 33 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 33 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 33 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 273 3 8 11 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 33 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 33 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 33 273 3 7 11 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 33 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 33 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 33 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 33 273 3 6 11 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 33 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 33 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 33 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 33 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 273 3 5 11 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 33 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 33 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 33 273 3 4 11 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 33 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 33 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 33 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 33 273 3 3 11 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 33 273
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 33 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 273 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 33 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 273 3 2 11 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 33 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 273
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 33 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 33 273 3 1 11 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 33 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 33 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 33 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 273)))))))))))))))))))))))))))))))))
  (allB_succ 32 273 (allA_succ_of_accept 31 32 273 (accept_3_4 31 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 32 273 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 32 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 32 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 32 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 32 273 (accept_3_4 28 32 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 32 273 (Polychromatic418967fa.accept_15_12_2_3_1_1146
  27 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 32 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 32 273 (accept_3_4 25 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  32 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 32 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 32 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 32 273 (accept_3_4 22 32 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 32 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 32 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 32 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 32 273 (accept_3_4 19 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  32 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 32 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 32 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 32 273 (accept_3_4 16 32 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 32 273 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 32 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 32 273
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 32 273 (accept_3_4 13 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  32 273 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 32 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 32 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 32 273 (accept_3_4 10 32 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 32 273 (Polychromatic418967fa.accept_17_9_15_1_1_7048 9 32 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 32 273
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 32 273 (accept_3_4 7 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 32
  273 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 32 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 32 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 32 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 32 273 (accept_3_4 4 32 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 32 273 (Polychromatic418967fa.accept_14_3_4_7_1_175 3 32 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 32 273 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 32
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 32 273 (accept_3_4 1 32 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32 273)))))))))))))))))))))))))))))))) (allB_succ 31 273
  (allA_succ_of_accept 30 31 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 273 (accept_3_5 29 31 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 31 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 31 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009
  27 31 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 273 (accept_3_5 26
  31 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 273
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 31 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 31 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 31 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 273 (accept_3_5 23 31 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 31 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 273 (Polychromatic418967fa.accept_15_6_1_3_1_2852
  21 31 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 273 (accept_3_5 20
  31 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 273
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 31 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 31 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 273 (accept_3_5 17 31 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 31 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 31 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  31 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 273 (accept_3_5 14 31
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 273
  (Polychromatic418967fa.accept_15_13_1_3_1_1972 13 31 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 31 273 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 31 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 273 (accept_3_5 11 31 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 31 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 273 (Polychromatic418967fa.accept_18_9_13_3_1_5088
  9 31 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 273 (accept_3_5 8 31
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 273 (Polychromatic418967fa.accept_9_7_4_3_1_204
  7 31 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 273 (accept_3_5 5 31 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 31 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 31 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 273 (accept_3_5 2 31 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 31 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 273))))))))))))))))))))))))))))))) (allB_succ 30 273
  (allA_succ_of_accept 29 30 273 (Polychromatic418967fa.accept_16_13_14_1_1_2094 29 30 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 30 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 30 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 30 273 3 9 10 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 30 273
  (Polychromatic418967fa.accept_12_2_6_9_1_19 26 30 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 30 273 (Polychromatic418967fa.accept_18_7_12_3_1_804 25 30 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 273 3 8 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 30 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 273
  (Polychromatic418967fa.accept_12_10_6_9_1_549 22 30 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 30 273 3 7 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 30 273 (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 30 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 30 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 273 3 6 10 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 273
  (Polychromatic418967fa.accept_20_17_10_13_1_1400 17 30 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 30 273 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 30 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 30 273 3 5 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 30 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  30 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 30 273
  (Polychromatic418967fa.accept_16_13_14_1_1_2094 13 30 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 273 3 4 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 30 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 30 273 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 30 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 30 273 3 3 10 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 30 273
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 30 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 30 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 273 3 2 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 273 (Polychromatic418967fa.accept_14_5_2_7_1_2804 5 30 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 30 273
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 30 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 30 273 3 1 10 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 30 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 30 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 273 (Polychromatic418967fa.accept_18_1_12_3_1_6426 1 30 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 273)))))))))))))))))))))))))))))) (allB_succ
  29 273 (allA_succ_of_accept 28 29 273 (accept_3_4 28 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 29 273 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 29 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 29 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 273 (accept_3_4 25 29 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 24
  29 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 273 (accept_3_4 22 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 273 (Polychromatic418967fa.accept_16_5_13_1_1_2084 21 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 29 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 273 (accept_3_4 19 29 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 273 (Polychromatic418967fa.accept_19_18_10_7_1_3174 18 29 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 273
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 273 (accept_3_4 16 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 29 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 273 (accept_3_4 13 29 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 29 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 273
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 273 (accept_3_4 10 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 273 (Polychromatic418967fa.accept_16_9_13_1_1_3069 9 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 29 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 273 (accept_3_4 7 29 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 29 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 273 (accept_3_4 4 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  273 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 29 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 29 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 273 (accept_3_4 1 29 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 273))))))))))))))))))))))))))))) (allB_succ 28 273 (allA_succ_of_accept 27 28 273
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 28 273 (accept_3_5 26 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  28 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 28 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 28 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 28 273 (accept_3_5 23 28 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 28 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 28 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 28 273 7 3 4 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 28 273 (accept_3_5 20 28 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 28 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 273
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 273 (accept_3_5 17 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 28 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 273 7 2 4 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13
  28 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 273
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 273 (accept_3_5 11 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 273 (Polychromatic418967fa.accept_15_10_13_3_1_4816 10 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 273 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 28 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 273 (accept_3_5 8 28 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 28 273 7 1 4 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 28 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 28 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 28 273 (accept_3_5 5 28 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 28 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 28 273
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 28 273 (accept_3_5 2 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 28
  273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 28 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 28 273)))))))))))))))))))))))))))) (allB_succ 27 273 (allA_succ_of_accept 26 27 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 27 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 273 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 27 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 273 3 8 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 27 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 27 273 3 7 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 27 273 (Polychromatic418967fa.accept_14_6_13_7_1_2015 20 27 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 273 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 27 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 27 273 3 6 9 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 27 273
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 27 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 273 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 27 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 273 3 5 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 27 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 273
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 27 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 27 273 3 4 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 27 273 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 27 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 27 273 3 3 9 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 27 273
  (Polychromatic418967fa.accept_14_8_13_7_1_2798 8 27 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 273 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 27 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 273 3 2 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 273 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 27 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 273
  (Polychromatic418967fa.accept_10_4_7_3_1_54 4 27 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 27 273 3 1 9 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 27 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 27 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 273 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 27 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 273))))))))))))))))))))))))))) (allB_succ 26
  273 (allA_succ_of_accept 25 26 273 (accept_3_4 25 26 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 26 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 26 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 26 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 26 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 26 273 (accept_3_4 22 26 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 26 273 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 26 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 26 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 26 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 26 273 (accept_3_4 19 26 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  26 273 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 26 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 26 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 26 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 26 273 (accept_3_4 16 26 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 26 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 26 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 26 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 26 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 26 273 13 1 2 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 26 273 (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 26 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 26 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 26 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 26 273 (accept_3_4 10 26 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 26 273 (Polychromatic418967fa.accept_10_9_6_3_1_545 9
  26 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 26 273
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 26 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 26 273 (accept_3_4 7 26 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 26
  273 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 26 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 26 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 26 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 26 273 (accept_3_4 4 26 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 26 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 26 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 26 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 2
  26 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 26 273 (accept_3_4 1 26 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26 273)))))))))))))))))))))))))) (allB_succ 25 273
  (allA_succ_of_accept 24 25 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 25 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 273 (accept_3_5 23 25 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 25 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 273 (Polychromatic418967fa.accept_15_6_10_3_1_2844
  21 25 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 273 (accept_3_5 20
  25 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 273
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 25 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 273 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 25 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 273 (accept_3_5 17 25 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 25 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 15
  25 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 273 (accept_3_5 14 25
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 273 (Polychromatic418967fa.accept_9_4_7_3_1_43
  13 25 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 273
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 25 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 273 (accept_3_5 11 25 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 25 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 273 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 25 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 273 (accept_3_5 8 25 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 273 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 25 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 25 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 273 (accept_3_5 5 25 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 25 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 25 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 25 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 273 (accept_3_5 2 25 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 25 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 25 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 273))))))))))))))))))))))))) (allB_succ 24 273
  (allA_succ_of_accept 23 24 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 24 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 24 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 24 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 24 273 3 7 8 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 24 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 24 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 24 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 24 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 273 3 6 8 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 24 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 24 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 24 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 24 273 3 5 8 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 24 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 24 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 24 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 273 3 4 8 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 24 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 24 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 24 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 24 273 3 3 8 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 24 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 24 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 24 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 273 3 2 8 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 24 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 24 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 24 273 3 1 8 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 24 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 24 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 24 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 24 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 24 273)))))))))))))))))))))))) (allB_succ 23 273 (allA_succ_of_accept 22 23
  273 (accept_3_4 22 23 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 273
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 23 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 23 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 273 (accept_3_4 19 23 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 23 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 273 (Polychromatic418967fa.accept_9_8_5_3_1_777 17
  23 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 273 (accept_3_4 16 23
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 273
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 23 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 23 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 23 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 273 (accept_3_4 13 23 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 23 273 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 23 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 273
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 23 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 273 (accept_3_4 10 23 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 273 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 23 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 23 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 273 (accept_3_4 7 23 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 23 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 273
  (Polychromatic418967fa.accept_14_5_9_7_1_590 5 23 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 273 (accept_3_4 4 23 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  273 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 23 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 23 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 23 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 273 (accept_3_4 1 23 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 23 273))))))))))))))))))))))) (allB_succ 22 273 (allA_succ_of_accept 21 22 273
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 22 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 273 (accept_3_5 20 22 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 273 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 22 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 273 (accept_3_5 17 22 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 22 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 273
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 273 (accept_3_5 14 22 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 22 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 273 (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 22 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 273 (accept_3_5 11 22 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 22 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 273
  (Polychromatic418967fa.accept_20_9_2_13_1_6778 9 22 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 273 (accept_3_5 8 22 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 273 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 22 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 273 (accept_3_5 5 22 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 273 (Polychromatic418967fa.accept_15_4_7_3_1_119 4 22 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 273 (accept_3_5 2 22 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 22
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 273)))))))))))))))))))))) (allB_succ 21
  273 (allA_succ_of_accept 20 21 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 21 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 273 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 21
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 273 3 6 7 91 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 273
  (Polychromatic418967fa.accept_19_17_2_7_1_11422 17 21 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 273 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 21 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 273 3 5 7 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 21 273 7 2 3 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 21 273 (Polychromatic418967fa.accept_16_13_5_1_1_3017 13 21 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 21 273 3 4 7 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 21 273
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 21 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 21 273 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 21 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 273 3 3 7 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 273 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 21 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 21 273 7 1 3 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 21 273 3 2 7 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 273
  (Polychromatic418967fa.accept_15_5_6_3_1_525 5 21 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 273 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 21 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 21 273 3 1 7 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 21 273 (Polychromatic418967fa.accept_10_2_1_3_1_233 2 21 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 273
  (Polychromatic418967fa.accept_11_1_10_9_1_871 1 21 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 21 273))))))))))))))))))))) (allB_succ 20 273 (allA_succ_of_accept 19 20 273 (accept_3_4 19 20 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 20 273 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 20 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 20 273
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 20 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 20 273 (accept_3_4 16 20 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  20 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 20 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 20 273 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 20 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 20 273 (accept_3_4 13 20 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 20 273 (Polychromatic418967fa.accept_16_12_4_1_1_1257 12 20 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 20 273
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 20 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 20 273 (accept_3_4 10 20 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  20 273 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 20 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 20 273 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 20 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 20 273 (accept_3_4 7 20 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 20 273 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 20 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 20 273
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 20 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 20 273 (accept_3_4 4 20 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 20
  273 (Polychromatic418967fa.accept_16_3_4_1_1_2996 3 20 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 20 273 (Polychromatic418967fa.accept_15_2_5_3_1_552 2 20 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 20 273 (accept_3_4 1 20 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 20 273)))))))))))))))))))) (allB_succ 19 273 (allA_succ_of_accept 18 19 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 273 (accept_3_5 17 19 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 19 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 19 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 273 (accept_3_5 14 19 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 19 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 273
  (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 19 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 273 (accept_3_5 11 19 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 273 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 19 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 273 (accept_3_5 8 19 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 273 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 19 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 273 (accept_3_5 5 19 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 19 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 19 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 273 (accept_3_5 2 19 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 273 (Polychromatic418967fa.accept_15_1_4_3_1_1928 1 19 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 273))))))))))))))))))) (allB_succ 18 273 (allA_succ_of_accept 17
  18 273 (Polychromatic418967fa.accept_14_3_4_7_1_175 17 18 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 18 273 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 18 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 18 273 3 5 6 91 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 18 273 (Polychromatic418967fa.accept_12_2_6_9_1_19 14
  18 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 18 273
  (Polychromatic418967fa.accept_11_2_7_9_1_890 13 18 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 18 273 3 4 6 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 18 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 18 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 273 (Polychromatic418967fa.accept_12_10_6_9_1_549 10 18 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 18 273 3 3 6 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 18 273
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 18 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 18 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 273 3 2 6 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 273 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 18 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 273
  (Polychromatic418967fa.accept_12_4_6_9_1_548 4 18 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 18 273 3 1 6 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 18 273 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 18 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18 273 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 18 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 273)))))))))))))))))) (allB_succ 17 273
  (allA_succ_of_accept 16 17 273 (accept_3_4 16 17 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  17 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 17 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 17 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 17 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 273 (accept_3_4 13 17 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 17 273 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 17 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 273
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 17 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 17 273 (accept_3_4 10 17 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  17 273 (Polychromatic418967fa.accept_19_9_17_7_1_12793 9 17 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 17 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 17 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 17 273 (accept_3_4 7 17 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 17 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 17 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 17 273
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 17 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 17 273 (accept_3_4 4 17 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 17
  273 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 17 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 17 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 17 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 273 (accept_3_4 1 17 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 17 273))))))))))))))))) (allB_succ 16 273 (allA_succ_of_accept 15 16 273
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 16 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 16 273 (accept_3_5 14 16 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  16 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 16 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 16 273 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 16 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 16 273 (accept_3_5 11 16 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 16 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 16 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 16 273
  (Polychromatic418967fa.accept_10_9_6_3_1_545 9 16 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 16 273 (accept_3_5 8 16 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 16
  273 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 16 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 16 273 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 16 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 16 273 (accept_3_5 5 16 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 16 273 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 16 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 16 273 (Polychromatic418967fa.accept_20_3_16_13_1_8307
  3 16 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 273 (accept_3_5 2 16
  273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 16 273 (Polychromatic418967fa.accept_6_1_4_3_1_14
  1 16 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 273)))))))))))))))) (allB_succ 15
  273 (allA_succ_of_accept 14 15 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 15 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 15 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 273 3 4 5 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 273
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 15 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 15 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 273 3 3 5 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 273 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 15 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 273
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 15 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 273 3 2 5 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 273 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 15 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 15 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 273 3 1 5 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 15 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 273 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 15 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 273))))))))))))))) (allB_succ 14 273 (allA_succ_of_accept 13 14 273
  (accept_3_4 13 14 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 14 273
  (Polychromatic418967fa.accept_18_12_14_3_1_2655 12 14 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 14 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 14 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 14 273 (accept_3_4 10 14 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 14 273 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 14 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 14 273 (Polychromatic418967fa.accept_9_8_5_3_1_777 8
  14 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 14 273 7 1 2 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 14 273
  (Polychromatic418967fa.accept_9_6_5_3_1_205 6 14 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 14 273 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 14 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 14 273 (accept_3_4 4 14 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 14 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 14 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 14 273 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 14
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 14 273 (accept_3_4 1 14 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 273)))))))))))))) (allB_succ 13 273 (allA_succ_of_accept 12 13
  273 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 13 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 273 (accept_3_5 11 13 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 273 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 13 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 273 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 13 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 273 (accept_3_5 8 13 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 273 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 13 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 273
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 13 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 273 (accept_3_5 5 13 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  273 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 13 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 273 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 13 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 273 (accept_3_5 2 13 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 273 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 13 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 273))))))))))))) (allB_succ 12 273 (allA_succ_of_accept 11 12
  273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 12 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 12 273 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 12 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 12 273 3 3 4 91 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 12 273
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 12 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 12 273 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 12 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 273 3 2 4 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 273 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 12 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 273
  (Polychromatic418967fa.accept_16_4_12_1_1_1204 4 12 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 12 273 3 1 4 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 12 273 (Polychromatic418967fa.accept_14_2_12_7_1_617 2 12 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12 273 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 12 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 273)))))))))))) (allB_succ 11 273
  (allA_succ_of_accept 10 11 273 (accept_3_4 10 11 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  11 273 (Polychromatic418967fa.accept_19_9_11_7_1_5836 9 11 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 11 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 11 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 273 (accept_3_4 7 11 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 11 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 273
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 11 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 11 273 (accept_3_4 4 11 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11
  273 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 11 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 11 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 11 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 273 (accept_3_4 1 11 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 11 273))))))))))) (allB_succ 10 273 (allA_succ_of_accept 9 10 273
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 10 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 10 273 (accept_3_5 8 10 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10
  273 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 10 273 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 10 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 10 273 (accept_3_5 5 10 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 10 273 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 10 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 273 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 273 (accept_3_5 2 10 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 273 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 10
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 273)))))))))) (allB_succ 9 273
  (allA_succ_of_accept 8 9 273 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 9 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 273 (Polychromatic418967fa.accept_18_7_9_3_1_800 7 9 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 273 3 2 3 91 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 273
  (Polychromatic418967fa.accept_14_5_9_7_1_590 5 9 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 273 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 9 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 9 273 3 1 3 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 9 273 (Polychromatic418967fa.accept_14_2_9_7_1_5633 2 9 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 273
  (Polychromatic418967fa.accept_18_1_9_3_1_2672 1 9 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 9 273))))))))) (allB_succ 8 273 (allA_succ_of_accept 7 8 273 (accept_3_4 7 8 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 8 273 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 8 273 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 8 273
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 8 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 8 273 (accept_3_4 4 8 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 8 273
  (Polychromatic418967fa.accept_20_3_8_13_1_3832 3 8 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 8 273 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 8 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 8 273 (accept_3_4 1 8 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 273)))))))) (allB_succ 7 273 (allA_succ_of_accept 6 7 273
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 273 (accept_3_5 5 7 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 273
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 7 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 273 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 7 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 273 (accept_3_5 2 7 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 273 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 7 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 273))))))) (allB_succ 6 273 (allA_succ_of_accept 5 6 273
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 6 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 6 273 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 6 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 6 273 3 1 2 91 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 6 273 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 6 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 6 273
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 6 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 6 273)))))) (allB_succ 5 273 (allA_succ_of_accept 4 5 273 (accept_3_4 4 5 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 5 273 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 5 273 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 273 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 5
  273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 273 (accept_3_4 1 5 273
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 273))))) (allB_succ 4 273 (allA_succ_of_accept 3 4 273
  (Polychromatic418967fa.accept_14_3_4_7_1_175 3 4 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 273 (accept_3_5 2 4 273 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 273
  (Polychromatic418967fa.accept_6_1_4_3_1_14 1 4 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 273)))) (allB_succ 3 273 (allA_succ_of_accept 2 3 273 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 3 273
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 273
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 3 273 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 3 273))) (allB_succ 2 273 (allA_succ_of_accept 1 2 273 (accept_3_4 1 2 273 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 2 273)) (allB_two
  273))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


